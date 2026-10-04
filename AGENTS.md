# Complexitylib — Agent Guide

This is the shared instruction source for coding agents in this repository.
`CLAUDE.md` points here; maintain repository guidance in this file.

## Project Overview

A Lean 4 library formalizing computational complexity theory, built on Mathlib. The machine model is shaped by Arora and Barak's *Computational Complexity: A Modern Approach* — a concrete 4-symbol alphabet and separate deterministic/nondeterministic machine types — but the library sets its own conventions and diverges from any one text where a cleaner formalization exists. NTMs and PTMs share the same structure (two transition functions); they differ only in acceptance semantics (existential vs counting).

For project direction, read the blueprint (`blueprint/`, published at
https://samuelschlesinger.github.io/complexitylib/blueprint/) for what is
formalized and planned, and `ROADMAP.md` for proof strategy and infrastructure
priorities, before beginning a large feature. Prefer landing one reusable
definition or intermediate theorem layer at a time. When a change formalizes a
blueprint node, add `\lean{...}` and `\leanok` to that node in the same change.

## Build

```bash
lake build --wfail Complexitylib \
  Complexitylib.Classes.P.Cobham.Validation \
  Complexitylib.Models.TuringMachine.SingleTape.Validation \
  Complexitylib.Models.TuringMachine.Repetition.Validation \
  Complexitylib.Circuits.Encoding.Validation \
  Complexitylib.SAT.Tseitin.Machine.Validation \
  ApiChecks runLinter
```

Always verify the library, all five executable validation roots, and the
seven isolated `ApiChecks` modules pass before considering a change complete.
One invocation shares Lake's dependency-graph work across the targets and
builds the upstream `runLinter` executable needed below. Validation and API
regressions remain outside the public import graph.

Quality gates (also run in CI; see CONTRIBUTING.md):

```bash
python3 scripts/lint_style.py        # headers, module docs, 100-col, _root_, imports, native_decide
python3 -m unittest discover -s scripts -p 'test_*.py'  # maintenance scripts
lake env python3 scripts/lint_environment.py  # same roots/checks, separate processes
lake env lean scripts/AxiomGuard.lean  # every project declaration on std axioms only
lake env lean scripts/BlueprintCheck.lean  # blueprint links, \leanok markers, node kinds, labels
```

Both linters are hard gates: any violation fails the run. The refactor cleared
and removed the former shrink-only baselines, so keep the tree clean. Suppress
a genuinely-intended env-lint with a documented inline `@[nolint …]` on the
declaration — never a project-level baseline.

Never use `native_decide` (or `decide +native`, `bv_decide`, `bv_check`)
outside the executable validation modules. `lint_style.py` rejects it in every `.lean` file except
files named `Validation.lean` outside the public import graph, where it closes
`example`s used as regression tests. The axiom guard's scope and limits (it
trusts the `.olean` files, allows `Classical.choice`, and cannot see
`example`s) are documented in the header of `scripts/AxiomGuard.lean`.

## Architecture

### Module Structure

```
Complexitylib.lean               — root import (re-exports everything)
Complexitylib/Models.lean        — aggregation import for computation models
Complexitylib/Models/TuringMachine.lean          — Γ, Dir3, TM, NTM, Cfg, step/trace, acceptance, Language
Complexitylib/Models/TuringMachine/Internal.lean — proof internals (e.g. toNTM_accepts_iff)
```

Aggregation files (`Complexitylib.lean`, `Models.lean`) contain only `import` statements — no definitions.

### Three-Layer Architecture

The codebase uses three layers to separate concerns:

1. **Definitions layer** (`Foo/Defs.lean`) — Core types, structures, and
   definitions. Imported by both Internal and surface layers. Minimal
   imports. Human-auditable: a reader should be able to verify that these
   definitions faithfully capture the intended concepts.
2. **Internal layer** (`Foo/Internal.lean` or `Foo/Internal/`) — Proof
   internals, helper lemmas, and auxiliary constructions. Imports `Foo/Defs`
   (not `Foo.lean`). Not meant for human review — correctness is
   established by the type checker.
3. **Surface layer** (`Foo.lean`) — Public theorem statements with proofs
   supplied by importing from Internal. Also human-auditable: a reader
   should be able to verify that the theorem types mean what they claim
   without understanding proof internals.

Import graph (no cycles):

```
Foo/Defs.lean ← Foo/Internal.lean
Foo/Defs.lean ← Foo.lean ← Foo/Internal.lean
```

The Defs layer exists to break the import cycle that would occur if Internal
needed to reference definitions from the surface layer. By extracting
definitions into `Defs.lean`, Internal modules can use proper named
definitions in their theorem signatures rather than raw expressions.

For simple modules where Internal proofs don't need to reference surface
definitions, the two-layer pattern (surface + Internal) is fine — introduce
`Defs.lean` when the need arises. For trivial proofs, `private` lemmas in the
same file are acceptable.

### Key Design Decisions

- **`Complexity` root namespace**: every declaration lives under `Complexity`
  (avoids collisions with Mathlib's `Language`, keeps `P`/`NP`/`TM` out of the
  root scope). Files are wrapped in `namespace Complexity … end Complexity`.
  Exceptions: `Complexitylib/Mathlib/` extends Mathlib types in their home
  namespaces (dot-notation requires it) and holds upstreaming candidates only;
  `Complexitylib/Cslib/` likewise extends CSLib types in their home namespaces
  (e.g. `Cslib.Circuits`) and holds upstreaming candidates only;
  `Complexitylib/Algebraic/` is the algebraic-circuits library imported
  wholesale, which keeps its `Algebraic` namespace, its `Cslib.Circuits`
  extensions, and a scoped style-lint exemption until the consolidation plan
  in `ROADMAP.md` (item 7) migrates it. It keeps its MIT license
  (`Complexitylib/Algebraic/LICENSE`), so its files carry the MIT header.
- **Never shadow a root namespace**: an inner `namespace TM` block inside
  another namespace (e.g. producing `SAT.TM`) shadows the real `TM.*` API and
  forces `_root_.` escapes — the style linter rejects `_root_.` outside the
  imported algebraic-circuits library.
- **Arora-Barak style**: Fixed alphabet `Γ = {0, 1, □, ▷}`, three-way directions (`Dir3`), explicit `qstart`/`qhalt` states.
- **Named tapes**: `Cfg` has separate `input : Tape`, `work : Fin n → Tape`, `output : Tape` fields. This avoids degenerate `Fin k` indexing and makes the read-only/read-write distinction structural.
- **DTM (`TM`)**: Single deterministic transition function `δ`. Execution via `step` (computable) and relational `stepRel`/`reaches`/`reachesIn`.
- **NTM (`NTM`)**: Two transition functions `δ₀, δ₁` selected by a `Bool`. Execution via `trace` (canonical, takes a fixed choice sequence). No parallel relational hierarchy — `trace` is the single source of truth.
- **Acceptance vs deciding**: `Accepts`/`AcceptsInTime` are existential. A DTM
  `DecidesInTime` by halting with output `1` on `x ∈ L` and exactly `0` on
  `x ∉ L`. An NTM `DecidesInTime` when every path halts and an accepting path
  exists exactly for `x ∈ L`; any halted path whose output cell is not `1` is
  rejecting. Use `NTM.RejectsWithZero` when a construction additionally needs
  exact `0` output on every rejecting path.
- **PTM counting**: `acceptCount` and `acceptProb` count/measure accepting
  fixed-length choice strings over `Fin T → Bool`. Meaningful only when all
  paths halt within `T` steps. This is distinct from the computation-tree leaf
  count used by `SharpP`.
- **Custom one-sided tapes**: `Tape` has `head : ℕ` and `cells : ℕ → Γ`. Cell 0 is leftmost and permanently `▷` (write is a no-op at cell 0). Moving left at position 0 is a no-op (Nat subtraction). Output is read from `cells 1` (first cell after `▷`). No dependency on `Mathlib.Computability.Tape`.
- **Read vs write alphabet**: `δ` reads `Γ = {0, 1, □, ▷}` but writes `Γw = {0, 1, □}`, structurally preventing writing `▷`. Combined with immutable cell 0, `▷` uniquely marks position 0 on every tape.
- **Finite state**: `TM` and `NTM` carry `[Fintype Q]`, matching AB's finite state requirement.

### Naming Conventions

Follow Mathlib style:
- `camelCase` for term-level definitions (`stepRel`, `initCfg`, `halted`, `trace`)
- `PascalCase` for types and Prop-valued definitions (`TM`, `NTM`, `Cfg`, `Accepts`, `DecidesInTime`)
- Namespace-qualified names for definitions that operate on a type (`TM.stepRel`, `NTM.trace`)

### Common Pitfalls

- **No `module` keyword** in aggregation files — they import files with definitions, and `module` files can only import other `module` files.
- **`List.get?` removed**: Use `l[i]?` (GetElem? syntax) instead of `l.get? i` in Lean 4 v4.28.0+.
- **Lambda expressions in conjunction chains** need explicit parens: `c'.work = (fun i => ...) ∧ ...`
- **`open` scoping**: Prefer `open Foo in` or `section`/`end` blocks over module-level `open` to avoid namespace pollution.
- **`DecidableEq Q` and `Fintype Q`**: The `TM` and `NTM` structures carry these as instance fields, exposed via `attribute [instance]`. `DecidableEq` is needed for `if c.state = tm.qhalt` in `step`/`trace`; `Fintype` matches AB's finite state requirement.
- **Existential binders**: Use `∃ (T : ℕ) (choices : Fin T → Bool), ...` with explicit type annotations — omitting them causes parse errors.

## Lean Proof Development Workflow

Develop proofs in checked increments. Use tools to resolve specific uncertainty
and obtain compiler feedback. Tool-call frequency is not a measure of rigor;
choose the cheapest reliable way to answer the next question.

### Work in coherent proof blocks

1. **Establish the statement and proof idea.** For an unfamiliar result, inspect
   the relevant definitions and theorem signatures, identify the mathematical
   argument, and check that the statement expresses the intended claim. Check
   a new dependent statement early, before building downstream proofs on it.
   A temporary `sorry` is useful for isolating a statement or subgoal; it is
   optional scaffolding, not a required first step, and must be removed before
   completion.
2. **Write the smallest useful unit.** Write a routine proof in full when the
   steps are understood. For a difficult proof, implement one helper lemma,
   induction branch, or coherent tactic block, then check it. Several tactics
   between checks are expected; there is no requirement to query Lean after
   each `intro`, `constructor`, or other predictable step.
3. **Inspect when uncertainty increases.** Use the actual goal and local context
   when elaboration surprises you, an induction hypothesis has an unexpected
   type, dependent case analysis changes the context, or a plausible closer
   fails for an unclear reason. Reduce the block size until the obstacle is
   understood. After a representative case works, reuse its pattern and check
   the resulting proof together; inspect other branches individually when
   their contexts materially differ.
4. **Check before expanding the dependency chain.** Confirm that each meaningful
   unit elaborates before building substantial work on top of it. Use focused
   diagnostics or a scoped build during development. A successful tactic probe
   still needs to be incorporated and checked in the actual file. Finish with
   the repository build and quality gates listed above; intermediate checks
   do not replace them.

### Choose tools by the question

- **Current goal or hypotheses:** use `lean_goal` at the relevant location.
  Inspect the unresolved part, rather than repeatedly dumping a whole file.
- **Does the edited unit elaborate?** Use `lean_diagnostic_messages` or
  `lake build --wfail <Module>`. Prefer a scoped build when changed imports
  or multiple dependent files are involved. Avoid obtaining the same feedback
  from several tools unless their results disagree or a required gate remains.
- **Which lemma applies?** Search local source or use `lean_local_search` first
  when a likely name or module is known. Use `lean_leansearch`, `lean_loogle`,
  or `lean_state_search` for a conceptual search. Inspect the selected lemma's
  actual signature instead of repeatedly guessing names or argument order.
- **Which of a few plausible closers works?** Use `lean_multi_attempt` when
  batching candidates is cheaper than separate edit/check cycles. Select
  candidates from the goal's structure; broad tactic spraying is not a proof
  strategy. Write an evident closer directly and check the resulting unit.
- Batch independent reads and searches where supported. Keep edits and checks
  that depend on those edits sequential. Reuse information already obtained
  until a relevant source change or diagnostic gives reason to refresh it.

### Recover from failures deliberately

- When attempts keep failing for the same reason, inspect the mismatch and
  reconsider the statement, induction generalization, or needed helper lemma.
  Repeating speculative tactics without new information is a cue to change
  approach.
- If diagnostics report stale imports or disagree with recently changed
  dependencies, build the smallest affected module and refresh diagnostics.
  If MCP/LSP results remain stale, use the scoped command-line build to check
  the saved source. Do not rewrite a working proof to accommodate stale state
  or keep polling unchanged diagnostics.
- If an MCP tool is unavailable, continue with source inspection and scoped
  Lean/Lake checks. Tool availability should not block work that the compiler
  can validate. Report the checks actually completed and any unresolved
  failures; never infer success from a tool returning no useful result.

### Practical tips

- When `omega` fails on a goal containing `match`/`if`/`max`:
  - **`match`**: use `cases` or `generalize x = s; cases s` to eliminate
    the match discriminant. If a pattern variable shadows an outer name
    (common with `cases ref with | work i =>`), add `dsimp only` first
    to reduce inner matches before `generalize`.
  - **`if`**: use `ite_true`/`ite_false` in simp, or `dsimp only` to
    reduce decided conditions. Alternatively, use `split` or `split_ifs`.
  - **`max`**: avoid `max_def` + `split` (fragile). Instead, use
    `le_max_left`/`le_max_right` directly for simple bounds, and
    `max_le`/`max_le_max_left` for transitivity through IH results.
    Pattern: `le_trans ih_result (max_le_max_left done (by simp [hns]; omega))`.
  - Use `first | tac1 | tac2` when different case-split branches need
    different strategies (e.g. `le_max_left` vs `le_max_right`).
- If the IH signature doesn't match what you expect, use `lean_goal` to
  inspect its exact type — the implicit arguments may already be
  specialized.
- Use `dsimp only` to reduce unreduced projections (`.1`, `.2`),
  constructor matches, and `let` bindings left behind by `simp only`.

## Commit Format

See CONTRIBUTING.md. Use `<type>(<scope>): <summary>` format with imperative mood.

## Dependencies

- **Lean**: `leanprover/lean4:v4.35.0-rc3` (see `lean-toolchain`)
- **Mathlib**: commit `728a93ee` (see `lakefile.toml`) — pinned to match the pinned cslib
  commit's `lake-manifest.json` so the foundations can be rebased onto
  [cslib](https://github.com/leanprover/cslib)
- **cslib**: commit `311d27ad` of [leanprover/cslib](https://github.com/leanprover/cslib) (see
  `lakefile.toml`). Pinned by commit `rev`, never a branch. Its Mathlib pin must equal ours, so a
  cslib bump dictates the Mathlib and toolchain bump. cslib ships no olean cache; Lake compiles
  only the cslib modules we import. CSLib circuit modules that are not upstream yet (relative
  complexity, circuit families with `SIZE` and `P/poly`, completeness of the De Morgan basis,
  circuit dependencies) live in `Complexitylib/Cslib/` under their `Cslib.*` namespaces.

When updating any of the three, all must be updated in lockstep: pick the cslib commit first, then
take its `lean-toolchain` and Mathlib `rev`. The `docbuild/` subproject pins the same toolchain
separately: bump `docbuild/lean-toolchain` and the `doc-gen4` `rev` (tagged per Lean release) in
`docbuild/lakefile.toml`, then regenerate its manifest with
`cd docbuild && MATHLIB_NO_CACHE_ON_UPDATE=1 lake update`. Any new root dependency also needs this
regeneration or the docs workflow fails with "not in manifest".

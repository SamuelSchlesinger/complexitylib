# Complexitylib — Agent Guide

## Project Overview

A Lean 4 library formalizing computational complexity theory, built on Mathlib. The machine model is shaped by Arora and Barak's *Computational Complexity: A Modern Approach* — a concrete 4-symbol alphabet and separate deterministic/nondeterministic machine types — but the library sets its own conventions and diverges from any one text where a cleaner formalization exists. NTMs and PTMs share the same structure (two transition functions); they differ only in acceptance semantics (existential vs counting).

For project direction and dependency-ordered contribution tracks, read
`ROADMAP.md` before beginning a large feature. Prefer landing one reusable
definition or intermediate theorem layer at a time.

## Build

```bash
lake build --wfail
lake build --wfail Complexitylib.Models.TuringMachine.SingleTape.Validation
lake build --wfail Complexitylib.Circuits.Encoding.Validation
```

Always verify all three commands pass before considering a change complete.
The latter two run executable regression guards that are intentionally kept
out of the public import graph.

Quality gates (also run in CI; see CONTRIBUTING.md):

```bash
python3 scripts/lint_style.py        # headers, module docs, 100-col, _root_ escapes
lake exe runLinter Complexitylib     # Mathlib/Batteries env linters
lake env lean scripts/AxiomGuard.lean  # headline theorems on std axioms only
```

Both linters are hard gates: any violation fails the run. The refactor cleared
and removed the former shrink-only baselines, so keep the tree clean. Suppress
a genuinely-intended env-lint with a documented inline `@[nolint …]` on the
declaration — never a project-level baseline.

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
  Sole exception: `Complexitylib/Mathlib/` extends Mathlib types in their home
  namespaces (dot-notation requires it) and holds upstreaming candidates only.
- **Never shadow a root namespace**: an inner `namespace TM` block inside
  another namespace (e.g. producing `SAT.TM`) shadows the real `TM.*` API and
  forces `_root_.` escapes — the style linter tracks and shrinks `_root_.` use.
- **Arora-Barak style**: Fixed alphabet `Γ = {0, 1, □, ▷}`, three-way directions (`Dir3`), explicit `qstart`/`qhalt` states.
- **Named tapes**: `Cfg` has separate `input : Tape`, `work : Fin n → Tape`, `output : Tape` fields. This avoids degenerate `Fin k` indexing and makes the read-only/read-write distinction structural.
- **DTM (`TM`)**: Single deterministic transition function `δ`. Execution via `step` (computable) and relational `stepRel`/`reaches`/`reachesIn`.
- **NTM (`NTM`)**: Two transition functions `δ₀, δ₁` selected by a `Bool`. Execution via `trace` (canonical, takes a fixed choice sequence). No parallel relational hierarchy — `trace` is the single source of truth.
- **Acceptance vs deciding**: `Accepts`/`AcceptsInTime` are existential. `DecidesInTime` requires halting on all inputs (DTM) or all paths (NTM), outputting `1` for `x ∈ L` and `0` for `x ∉ L` (matching AB Definitions 1.2 / 2.1 exactly).
- **PTM counting**: `acceptCount` and `acceptProb` count/measure accepting paths over `Fin T → Bool`. Meaningful only when all paths halt within `T` steps.
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

Develop proofs iteratively, not all at once. Use the LSP tools to stay
grounded in the actual proof state at every step.

### Core approach

1. **Start with `sorry`**: Stub out the theorem body with `sorry`, then use
   `lean_goal` or `lean_diagnostic_messages` to confirm the statement is
   well-typed and see the initial goal.
2. **Expand one tactic at a time**: Replace `sorry` with a tactic (e.g.
   `intro`, `induction`, `cases`, `simp`, `constructor`), followed by
   `sorry` for each remaining subgoal. Check the proof state after each
   step.
3. **Check proof state constantly**: Use `lean_goal` on the line/column of
   a `sorry` or tactic keyword to see the current hypotheses and goal.
   Never write multi-line tactic blocks blind.
4. **Use `lean_multi_attempt`** to test candidate closers (`simp`, `omega`,
   `exact?`, `aesop`) without editing the file.
5. **Use search tools** (`lean_leansearch`, `lean_loogle`,
   `lean_state_search`, `lean_local_search`) to find lemmas when stuck,
   rather than guessing names.

### Practical tips

- After `induction`/`cases`, check each branch's goal individually — they
  often differ in subtle ways.
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
- When a proof has many similar cases, get one working first, then
  replicate the pattern.
- If the IH signature doesn't match what you expect, use `lean_goal` to
  inspect its exact type — the implicit arguments may already be
  specialized.
- Use `dsimp only` to reduce unreduced projections (`.1`, `.2`),
  constructor matches, and `let` bindings left behind by `simp only`.

## Commit Format

See CONTRIBUTING.md. Use `<type>(<scope>): <summary>` format with imperative mood.

## Dependencies

- **Lean**: `leanprover/lean4:v4.34.0-rc2` (see `lean-toolchain`)
- **Mathlib**: commit `e06eff5f` (see `lakefile.toml`) — pinned to match [cslib](https://github.com/leanprover/cslib)'s `lake-manifest.json` so the foundations can be rebased onto it

When updating either, both must be updated in lockstep.

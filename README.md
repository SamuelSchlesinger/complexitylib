# Complexitylib

[![CI](https://github.com/SamuelSchlesinger/complexitylib/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/SamuelSchlesinger/complexitylib/actions/workflows/lean_action_ci.yml)

A Lean 4 formalization of computational complexity theory, built on
[Mathlib](https://github.com/leanprover-community/mathlib4). The machine
model takes its shape from Arora and Barak's *Computational Complexity: A
Modern Approach*, but the library sets its own conventions — stated
precisely where they're used, with literature references where they help,
and unafraid to diverge from any one text when a cleaner formalization
exists.

- 📖 **[API documentation](https://samuelschlesinger.github.io/complexitylib/)** —
  the full library, searchable, rebuilt on every merge to `dev`.
- 🗺️ **[Blueprint](https://samuelschlesinger.github.io/complexitylib/blueprint/)** —
  what is formalized, what is planned, and how it all depends on each other.

## Main results

All proved without `sorry` or custom axioms, over a concrete multi-tape
Turing-machine model:

- **Cook–Levin:** SAT and 3SAT are NP-complete.
- **Cobham's theorem:** a machine-independent function algebra equals `FP`.
- **Universal simulation:** one fixed machine simulates every machine through
  the computable compiler `p ↦ ⟨α, p⟩`, reflecting halting and output, with
  polynomial overhead.
- **Deterministic time hierarchy** for clock-constructible bounds.
- **Uniform circuits:** `P` equals logspace-uniform `P/poly`; `BPP ⊆ P/poly`.
- **Space and interaction:** Savitch's theorem (`NPSPACE = PSPACE`),
  `NL ⊆ P`, `PSPACE ⊆ EXP`, `IP ⊆ PSPACE`, `PH ⊆ PSPACE`, `PP ⊆ PSPACE`.
- **The PCP theorem:** `NP = PCP(O(log n), O(1))`.
- **Randomness:** Sipser–Lautemann (`BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ`), `BPP ⊆ PP`.
- **Circuits:** Shannon's bounds, Schnorr's bound for parity, Valiant's depth
  reduction, and Barrington's theorem (log-depth formulas and width-5
  permutation branching programs decide the same families).
- **Machine robustness:** the logarithmic-cost RAM and Turing machines define
  the same `P`.
- **CSLib interoperability:** our machines and CSLib's multi-tape machines
  simulate each other with constant-factor overhead, so `P` is exactly CSLib's
  polynomial time, and `DTIME`, `DTISP`, and `FP` transfer to CSLib's time and
  space measures; CSLib's regular languages are in `L`. Our circuits and
  CSLib's De Morgan circuits translate into each other with linear overhead,
  which characterizes `P/poly` in CSLib's model and brings Lupanov's
  `(1 + ε) 2ⁿ / n` upper bound into this library.

The blueprint links each result to its Lean statement and lists the
conditional results (for example, `NL = coNL` from `NL ⊆ coNL`) separately
from the unconditional ones.

## Ethos

**Statements you can audit, proofs you don't have to.** Every public theorem
is stated so a reader can check it means what it claims — concrete machine
model, explicit resource bounds, honest encodings — while the proof machinery
lives out of sight in `Internal` modules whose correctness is the type
checker's job, not yours.

**Concrete over abstract.** Machines, circuits, reductions, and encoders are
given as concrete definitions rather than bare existence claims. Constructions
parameterized by an abstract finite type may be noncomputable at Lean's
meta-level because choosing a canonical enumeration uses classical choice; the
machine or codec semantics remain explicit. Complexity is measured on real
encodings; parsing, malformed inputs, and output conventions are explicit.
Constructions expose an exact resource bound first and an asymptotic corollary
second.

**Nothing on faith.** The library has no `sorry` and no custom axioms:
`scripts/AxiomGuard.lean` mechanically audits every declaration compiled from
Complexitylib modules for dependencies beyond Lean's three standard axioms,
and CI enforces it — along with Mathlib's style and environment linters — on
every push.

**AI-assisted development.** This project uses AI coding assistants for proof
development, refactoring, documentation, and research exploration. AI-assisted
changes are held to the same standards as every other contribution: the public
statements must be auditable, Lean's kernel must check the proofs, and the full
build, linter, validation, and axiom-audit gates must pass. No mathematical
claim is accepted on the authority of an AI system.

## How to read the library

Everything lives in the `Complexity` root namespace and splits into areas,
each with its own entry module:

| Area | Import | What it is |
| --- | --- | --- |
| Machine models | `Complexitylib.Models` | Arora–Barak multi-tape Turing machines — deterministic, nondeterministic, probabilistic — and everything built from them: combinators, simulations, universal machines |
| Encodings | `Complexitylib.Encoding` | Machine-independent self-delimiting blocks, pairing, and rose-tree data encodings |
| Asymptotics | `Complexitylib.Asymptotics` | `=O`/`=o` notation on `ℕ → ℕ`, bridging to Mathlib's asymptotics |
| Time bounds | `Complexitylib.TimeConstructible` | Time-constructible bounds for hierarchy and separation results |
| Complexity classes | `Complexitylib.Classes` | `P`, `NP`, `BPP`, `PSPACE`, and friends; containments, closure properties, reductions, and the time-hierarchy theorem |
| SAT | `Complexitylib.SAT` | CNF semantics and encoding, a verified SAT verifier, and the Cook–Levin theorem: `SAT` is NP-complete |
| Circuits | `Complexitylib.Circuits` | Boolean circuits with size and depth, circuit families, `P/poly`, normal forms, and classical lower bounds |
| Boolean analysis | `Complexitylib.BooleanAnalysis` | Fourier expansion, noise stability, and influence for Boolean functions |
| Descriptive complexity | `Complexitylib.DescriptiveComplexity` | Finite structures, first- and second-order logic, definability, and model checking |
| Languages | `Complexitylib.Languages` | Concrete decidable languages exercising the machine API end to end |
| Mathlib prelude | `Complexitylib.Mathlib` | Extensions to Mathlib types in their home namespaces; candidates for upstreaming |

Within an area, modules follow one discipline:

- **`Foo/Defs.lean`** — definitions. Short, minimally-imported, auditable.
- **`Foo.lean`** — the surface: theorem statements worth reading.
- **`Foo/Internal…`** — proof machinery. Skip it; the type checker read it.

So: import `Complexitylib` (or one area), read `Defs` and surface files, and
trust the kernel for the rest. Headline results — Cook–Levin, universal-machine
simulation with explicit overhead, the deterministic time hierarchy — are
indexed in the root module `Complexitylib.lean` and mechanically guarded in `scripts/AxiomGuard.lean`.

## Building

Install [elan](https://github.com/leanprover/elan); Lean and Mathlib versions
are pinned (currently Lean v4.35.0-rc2, tracking the [cslib](https://github.com/leanprover/cslib) toolchain).

```bash
lake build --wfail
```

CI additionally runs five executable regression suites and three quality gates;
see [CONTRIBUTING.md](CONTRIBUTING.md) for the full list and the style guide.
API documentation builds with doc-gen4 from `docbuild/` and publishes to
[GitHub Pages](https://samuelschlesinger.github.io/complexitylib/) on every
merge to `dev` (and weekly, plus on demand via the workflow).

## Contributing

The [blueprint](https://samuelschlesinger.github.io/complexitylib/blueprint/)
shows which planned results are ready to work on; its sources are in
[`blueprint/`](blueprint/). [ROADMAP.md](ROADMAP.md) covers how to prove things
here and the infrastructure priorities. [CONTRIBUTING.md](CONTRIBUTING.md)
covers style, layering, naming, and commit conventions. Design notes for the
larger completed constructions live in `docs/`.

To cite Complexitylib, see [CITATION.cff](CITATION.cff).

## License

Licensed under the [Apache License, Version 2.0](LICENSE).

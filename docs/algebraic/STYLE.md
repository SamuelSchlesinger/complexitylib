# Library and API style

Algebraic is organized as a reusable circuit library with several active
research developments layered above it. These conventions keep that broad
surface navigable without forcing breaking renames on existing users.

## Imports and stability

- `import Complexitylib.Algebraic.Core` is the stable starting point for signatures,
  programs, circuits, semantics, costs, substitution, and translation.
- `import Complexitylib.Algebraic.Applications` exposes a small selection of ready-to-use
  compilers and flagship lower-bound endpoints under
  `Algebraic.Applications`.
- `import Complexitylib.Algebraic` remains the complete umbrella. Focused module imports are
  preferred in reusable downstream code.
- The two facade modules are the most deliberately curated surface. Other
  public declarations remain available, but deep research namespaces may grow
  as their developments evolve.

## Names and namespaces

- The foundational circuit types belong to `Cslib.Circuits`. Define methods
  extending those types in their canonical CSLib namespaces so field notation
  also works on values constructed upstream. Re-export existing public method
  names from `Algebraic` for source compatibility. Gate bases and research
  developments continue to live in their existing `Algebraic` namespaces.
- Types and namespaces use `UpperCamelCase`; declarations use `lowerCamelCase`.
  Existing public names follow this convention and should not be mass-renamed.
- A theorem name should state its conclusion or principal inequality. Use a
  suffix such as `_iff`, `_eq`, `_le`, or `_lowerBound` when it makes the
  result easier to discover.
- Keep helper declarations `private` when they are proof-local. Reusable but
  non-facade machinery belongs in a descriptive nested namespace rather than
  the root `Algebraic` namespace.
- Prefer shallow aliases in `Algebraic.Applications` over moving established
  declarations out of their defining namespaces. Where the underlying theorem
  exposes proof-specific certificates or encodings, provide a focused
  application module with a conventional mathematical premise instead of
  merely shortening the theorem name. The main Applications module is an
  umbrella; prefer its focused modules in downstream code.

## Theorem and simp discipline

- State all mathematical promises explicitly: cost model, finiteness,
  bounded fan-in, semantic construction, and any circuit-local restriction.
- Document public structures, fields, definitions, and theorems. Module
  docstrings should say what is proved and where its assumptions stop.
- Mark a theorem `@[simp]` only when its left-hand side is in simplifier normal
  form and the rule is a dependable part of the API. Redundant aliases should
  remain ordinary rewrite theorems.
- Remove unused typeclass assumptions. Use `@[nolint unusedArguments]` only
  when an assumption is mathematically necessary to prove a proposition but
  cannot occur syntactically in its conclusion.

## Validation

Before submitting a change, run Complexitylib's gates from the repository
root:

```sh
lake build --wfail
lake exe runLinter Complexitylib
lake env lean scripts/AxiomGuard.lean
python3 scripts/lint_style.py
```

`scripts/AxiomGuard.lean` checks every declaration compiled from a
Complexitylib module, including this library's private declarations and its
extensions in `Cslib.Circuits`, against the standard axiom allowlist
(`propext`, `Classical.choice`, `Quot.sound`). `scripts/lint_style.py` rejects
`native_decide` and requires every public module to be reachable from the
root `Complexitylib` import, so a new file must be imported by
`Complexitylib/Algebraic.lean` or one of its imports.

The standalone repository's downstream-style `AlgebraicTests` suite and its
import checker were not imported, and Complexitylib's executable `Validation`
modules do not cover this library. Examples that clarify a construction can
remain near their defining module; `example`s add no declaration, so the axiom
audit cannot see them.

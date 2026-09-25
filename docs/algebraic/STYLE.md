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

Before submitting a change, run:

```sh
lake build Algebraic AlgebraicTests --wfail
lake test
lake lint
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_imports.py
```

Public behavior belongs in the downstream-style `AlgebraicTests` suite.
Proof-local examples can remain near their defining module when they clarify a
construction, but they do not replace an import-level regression.

`AlgebraicTests.AxiomAudit` checks all library-owned declarations visible through
the public import, including extensions in `Cslib.Circuits` and transitive
private proof dependencies, against the standard logical axiom allowlist.
Unexported modern-module declarations unreachable from the public API are
outside the audit. Public import coverage is a separate CI gate: a new file
must be reachable from `Algebraic.lean` so that its public interface is built
and audited. New test files must be reachable from `AlgebraicTests.lean`.

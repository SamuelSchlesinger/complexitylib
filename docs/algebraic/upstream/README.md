# CSLib cost-module rehearsal

[cslib-cost.patch](cslib-cost.patch) is an isolated extraction of
[`Complexitylib/Algebraic/Cost.lean`](../../../Complexitylib/Algebraic/Cost.lean) against CSLib commit
`91ab23c78b12e6c9d6fe747fa3f55c2771dd376e`, checked on 2026-09-15.
It is a review artifact; no pull request has been opened.

The patch puts the operation-cost type and program/circuit cost API directly
in `Cslib.Circuits`, without the local compatibility exports. It uses modern
modules and adds a focused test of nonuniform gate weights, unused gates,
free input outputs, and unit cost. Both root import files include the additions.

## Reproduction and scope

Apply the patch to the named CSLib revision:

```sh
git apply --check /path/to/algebraic-circuits/docs/upstream/cslib-cost.patch
git apply /path/to/algebraic-circuits/docs/upstream/cslib-cost.patch
```

The isolated checkout used its own dependency manifest, including Mathlib
`87befc843c2b3a1be12f7fe9ba274d212b544348`, rather than this repository's
Mathlib pin. The patch applies cleanly to the unmodified target source.
The open circuit PRs #429, #890, and #891 do not add this cost module in the
file lists inspected on that date; recheck overlap before submitting.

The copied code preserves its MIT notices and includes `LICENSE.Algebraic`.
CSLib's header linter requires Apache wording. The local validation checkout
therefore set `weak.linter.style.header = false` in its `[leanOptions]` table
to test the technical integration while preserving those notices. **That
configuration change is not included in the patch.** Resolve the license/header
convention and rerun validation without this exception before submission.

With that recorded exception, these checks passed in the isolated checkout:

```sh
lake build --wfail --iofail
lake exe mk_all --check
lake test
lake lint
lake exe lint-style
lake exe checkInitImports
lake shake --add-public --keep-implied --keep-prefix Cslib.Computability.Circuit.Cost
```

The text-style command returned success and warned that the target checkout
has no `scripts/nolints-style.txt`, so it used an empty exception list. The
focused shake check reported no import changes. These are local command
results, not a hosted upstream CI run.

This rehearsal covers only weighted cost. It does not establish integration
readiness for translations, gate elimination, AC0, monotone bounds, or Fusion.
The broader [readiness record](../upstream-readiness.md) retains that scope.

Codex assisted with extraction, review, tests, and validation. Any eventual
PR must disclose that assistance under CSLib's contribution policy.

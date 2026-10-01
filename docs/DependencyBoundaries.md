# Dependency-boundary pilot: generic pair construction

First ownership slice of [#57](https://github.com/SamuelSchlesinger/complexitylib/issues/57).
The implementation has moved, unchanged, from
`Classes.NP.Internal.PairBuildTM` to `Models.TuringMachine.Subroutines.PairBuild`.
The latter is the supported direct import for generic machine clients.

Three real model clients now use it: `Witness.Verifier.Defs`,
`Witness.Verifier.Internal.Pair`, and `UTM.Internal.PairSelf`. Their old
model-to-NP dependency edges are deleted. The old NP path is a compatibility
re-export, retained by the legacy SAT guess/verify route. It contains no
implementation and is removable only in an announced breaking release after
remaining clients migrate. Names, proof statements, machine definitions,
instances, transparency, and the exact `4 * xLen + 2 * yLen + 10` bound are
unchanged; the implementation file is byte-for-byte the original.

## Reproduce the source audit

Run the current script against both fixed trees, without changing checkouts:

```sh
python3 scripts/audit_imports.py --ref 858514cfaff12943e36326a4897a3cbde9567f80 \
  Complexitylib.Classes.NP.Internal.PairBuildTM \
  Complexitylib.Models.TuringMachine.Witness.Verifier.Defs \
  Complexitylib.Models.TuringMachine.Witness.Verifier \
  Complexitylib.Models.TuringMachine.UTM.Internal.PairSelf
python3 scripts/audit_imports.py --ref HEAD \
  Complexitylib.Classes.NP.Internal.PairBuildTM \
  Complexitylib.Models.TuringMachine.Subroutines.PairBuild \
  Complexitylib.Models.TuringMachine.Witness.Verifier.Defs \
  Complexitylib.Models.TuringMachine.Witness.Verifier \
  Complexitylib.Models.TuringMachine.UTM.Internal.PairSelf
```

The script resolves each ref once and prints its exact commit plus sorted
module lists. It reads Git's committed sources, ignoring worktree edits, and
uses the same import reader as the style and documentation-cache checks.
Counts below include the root and only project modules:

| Entry point | Source closure before/after | Public-import closure before/after |
| --- | --- | --- |
| Pair builder (old/new owner) | 11 / 11 | 11 / 11 |
| Witness.Verifier.Defs | 76 / 76 | 72 / 72 |
| Witness.Verifier | 85 / 85 | 73 / 73 |
| UTM.Internal.PairSelf | 19 / 19 | 19 / 19 |
| Old NP compatibility path | 11 / 12 | 11 / 12 |

Public-import closure means a graph of syntactically public edges, including
ordinary imports in legacy non-module files. It is **not** an elaborator
memory measurement or a count of accessible declarations. Meta imports still
count as source dependencies. Generic verifier and pair-self closures now
contain **zero NP modules**. Potential reverse source fan-out changes from 92
for the old implementation to 93 for the new owner (the compatibility wrapper
adds one); the old path alone is now reachable from 7 modules. These are
potential dependencies, not observed rebuild counts.

## Controlled warm rebuild probe

Measured on the same shared Linux executor with Lean `v4.35.0-rc3`, unchanged
package pins, `LEAN_NUM_THREADS=2`, and existing caches. Before: `858514cf`.
After: the unchanged implementation at the new owner. For each state, first
warm the exact targets below, then time the same command with no source edit:

```sh
lake build --wfail \
  Complexitylib.Models.TuringMachine.Witness.Verifier.Defs \
  Complexitylib.Models.TuringMachine.UTM.Internal.PairSelf \
  Complexitylib.SAT.Internal.GuessVerify
```

Next, only in the current implementation file, temporarily change the private
`pair_build_cons_eq` proof from `simp [pair]` to
`exact Eq.trans (by simp [pair]) rfl`, run that command, restore the exact source,
and run it again. Do not commit the probe. No definition or signature changes.

| Probe | Before elapsed | After elapsed | Actually rebuilt |
| --- | --- | --- | --- |
| Warm no-op | 1.528 s | 1.558 s | None |
| Private proof edit | 9.699 s | 9.651 s | Only the pair-builder implementation |
| Exact source restored | 9.901 s | 9.704 s | Only the pair-builder implementation |

Single samples do not establish a timing improvement. The one-time migration
rebuild is excluded from these steady-state samples. Cold builds were not run
or caches removed, and no artificial public-signature change was introduced.
The private-proof probe demonstrates why reverse source closure is not a
rebuild measurement; it does not establish behavior for other kinds of edits.

This slice removes an ownership inversion, **not** implementation lines or
source-module count. The unchanged 2,272-line implementation remains, and the
shim, small audit, regression checks, and this document are new infrastructure.
Narrowing proof exposure, splitting definitions, and reducing other public
aggregator dependencies remain separate work under #57.

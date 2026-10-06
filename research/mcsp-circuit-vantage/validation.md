# Validation record

[Back to the overview](index.md).

These checks were run on 2026-10-06. Production sources match
`b030149cd09f755bfead55f473d670f0880eedb0`; changes in this exploration are
confined to `research/mcsp-circuit-vantage/`.

| Check | Result |
| --- | --- |
| Required combined `lake build --wfail` command from `AGENTS.md` | Passed, 7,783 jobs; library, five validation roots, seven API modules, and `runLinter`. |
| `python3 scripts/lint_style.py` | Passed, no violations. |
| Maintenance `unittest` discovery | All 29 tests passed. |
| `lake env python3 scripts/lint_environment.py` | Passed for the configured library and validation roots. |
| `lake env lean scripts/AxiomGuard.lean` | 100,099 declarations, including 74,108 theorems and zero project axioms, from 3,746 modules use only standard axioms. |
| `lake env lean scripts/BlueprintCheck.lean` | 1,352 nodes and 4,970 declaration references in 18 files are consistent. |
| `lake env lean research/mcsp-circuit-vantage/data/RepeatedAnchor.lean` | Passed. The accepted-completion theorem uses `propext`, `Classical.choice`, and `Quot.sound` only. |
| Formal inventory probe | 32 declarations and nine standard-axiom reports passed. |
| Finite and arithmetic scripts | Passed; expected outputs are linked from the overview. |

The research theorem is outside the production import graph and hence outside
the production axiom guard's declaration set. Its own axiom report is checked
separately by the corpus audit. No native evaluation, unproved axiom, or `sorry`
is used in the research Lean artifact. These checks do not establish a
superlinear MCSP lower bound.

The [audit runner](data/audit.py) is the reproducible check for this corpus;
repository-wide gates use the commands in `AGENTS.md`.

The first independent review checked the mathematical transfers, all validation
artifacts, and primary-source statements. Revisions made the missing-pattern
lemma's proper-subset premise explicit, restored the parameter range in the
probabilistic formula result, added the checked raw-family average-case theorem
and its randomized-refuter consequence, and separated frontier witness search
from gate elimination. Prior local notes are now archived with checked hashes
instead of an unverifiable commit identity. The complete corpus audit passed
again after these revisions.

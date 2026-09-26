# Algebraic

> **Imported library.** This is the guide of the algebraic-circuits library, imported
> wholesale into Complexitylib as `Complexitylib/Algebraic/` (module paths
> `Complexitylib.Algebraic.*`; declarations keep the `Algebraic` namespace). It
> builds as part of Complexitylib's `lake build` and is checked by Complexitylib's
> gates (see [Build and checks](#build-and-checks)). See `ROADMAP.md` (item 7) for
> the plan to consolidate it with Complexitylib's circuit developments.
> Imported on 2026-09-25 from the algebraic-circuits working tree (commit
> `3998dc4` plus uncommitted changes that move it to Complexitylib's Lean, Mathlib,
> and CSLib pins), converted to Lean's module system with minimal edits and no
> changes to theorem statements. Later changes in Complexitylib alter statements
> only where needed: the port to the pinned CSLib fork (a circuit's gate count is
> now its `size` field rather than a type index, and wires are CSLib's inductive
> `Wire`), and a faithful restatement of the KRW conjecture (see the
> [Karchmer–Wigderson guide](karchmer-wigderson.md)). The standalone repository's
> regression suite (`AlgebraicTests`), import checker, research notes, and
> documentation scripts were not imported. It keeps its MIT license
> ([`Complexitylib/Algebraic/LICENSE`](../../Complexitylib/Algebraic/LICENSE)).

Algebraic is a Lean 4 library for finite-arity universal algebra and shared
circuit computation built on [CSLib](https://github.com/leanprover/cslib).
It extends CSLib's circuit model with semantics, costs, translations,
analyses, and lower-bound frameworks without fixing a particular carrier or
gate basis.

## Design

The signatures, interpretations, homomorphisms, wires, programs, and circuits
come from `Cslib.Computability.Circuit`. The `Algebraic` core imports re-export
these types and their operations, so native CSLib circuits work directly with
the library's constructions and lower bounds. Complexitylib's `lakefile.toml`
pins CSLib to commit `2a4389ba8d47778cafdd79f522f0b17b623b18b7`, the head of
the `complexitylib-integration` branch of the author's fork
(`SamuelSchlesinger/cslib`), with its matching Lean (`v4.35.0-rc3`) and Mathlib
versions. That branch contains upstream `main` at
`94ea80f41a5678fce997a004f0d8d12dbe47cc4b`, which includes the merged
[Shannon #891](https://github.com/leanprover/cslib/pull/891) and
[Lupanov #890](https://github.com/leanprover/cslib/pull/890) circuit
developments, and integrates pending CSLib circuit pull requests, among them
bundled gate counts ([#949](https://github.com/leanprover/cslib/pull/949)) and
inductive wires ([#957](https://github.com/leanprover/cslib/pull/957)). The pin
returns to a `leanprover/cslib` commit once that work lands.

- A `Signature` describes operation symbols and their arities, while an
  `Interpretation` assigns them concrete meaning.
- A `Program` is a topologically ordered, shared computation. A `Circuit`
  designates input or gate wires as outputs, so projections and multi-output
  circuits do not need artificial output gates.
- `circuit.ComputesWith interpretation target` expresses generic computation
  of a tuple-valued target. CSLib's `circuit.Computes interpretation function`
  is the single-output form. The former generic name remains available as
  `Algebraic.Circuit.Computes`.
- Homomorphisms connect interpretations. Translations implement one signature
  by circuits over another and carry semantic and weighted-cost guarantees.
- Structural and abstract analyses are kept separate from concrete bases, so
  they can be transported through translations and reused by lower-bound
  arguments.

Reusable Boolean, arithmetic, and sum-of-terms bases live under
`Algebraic.Basis`. The main `Algebraic` module is the umbrella import; focused
imports are available throughout the directory tree.

Choose an entry point for the task:

- `import Complexitylib.Algebraic.Core` for signatures, shared circuits, semantics, costs,
  substitution, and translation;
- `import Complexitylib.Algebraic.Complexity.Relative` for computing a target from supplied
  functions on an arbitrary common domain;
- `import Complexitylib.Algebraic.ConditionalComplexity` for the minimum cost of
  `h(x, g₀(x), …)`, free supplied values, and composition inequalities;
- `import Complexitylib.Algebraic.ConditionalComplexity.Linear` for exact complexity with
  linear Boolean helpers; see [conditional lower bounds](conditional-complexity.md#six-lower-bound-results-checked-in-lean)
  for support, Hessian, preprocessing, restriction, and approximation results;
- `import Complexitylib.Algebraic.Applications` for the umbrella of curated binary-power and
  lower-bound endpoints; prefer focused application imports when possible;
- `import Complexitylib.Algebraic.Basis.DeMorgan.Complexity` for minimum native circuit
  size, point updates, and the Hamming Lipschitz bound;
- `import Complexitylib.Algebraic.Basis.DeMorgan.PairIndicator` for support/read-once
  arguments and native size bounds for functions with two exceptional inputs;
- `import Complexitylib.Algebraic.LowerBound.Cutwidth` for the `(4 - ε) n` lower bound over
  the full binary basis; see the [cutwidth guide](cutwidth-lower-bound.md)
  for its two black-box hypotheses;
- `import Complexitylib.Algebraic.LowerBound.Nechiporuk` for the `Ω(n² / log n)` formula
  lower bound for the same rectangle-free functions; see the
  [Nechiporuk guide](nechiporuk-lower-bound.md);
- `import Complexitylib.Algebraic.LowerBound.KarchmerWigderson` for Karchmer–Wigderson
  games, the theorem identifying formula depth and size with protocol depth
  and size, and the statement of the KRW composition conjecture; see the
  [Karchmer–Wigderson guide](karchmer-wigderson.md);
- `import Complexitylib.Algebraic` for the complete library.

The naming, namespace, simp, and stability conventions are recorded in
[`STYLE.md`](STYLE.md).

See the [application guide](applications.md) for focused imports, cost
conventions, and checked examples. In particular,
`Algebraic.Applications.Hessian` accepts an ordinary polynomial computation
equality, and `Algebraic.Applications.Waring` accepts a finite sum-of-powers
equality. Neither interface requires callers to construct a Fusion certificate.

Elementary Boolean completeness is available from
`Algebraic.Basis.DeMorgan.Completeness`. Its truth-table construction and
multi-output completeness theorem do not depend on Lupanov synthesis or
minimum circuit complexity.

The [conditional complexity guide](conditional-complexity.md) explains
the relation to `Synthesis`, a checked counterexample to an exact chain rule,
and counting bounds for random targets with a fixed supplied family.

The point-update and counting arguments for strict circuit size hierarchies
are described in the [circuit hierarchy guide](circuit-hierarchy.md).
Basic Boolean operations, input masks, numerical thresholds, and the compiler
that shares constant gates remain available as focused modules under
`Algebraic.Basis.DeMorgan`.

## Lower bounds

`Algebraic.LowerBound` collects several independent methods, including
bounded-fan-in arguments, counting, gate elimination, and Fusion.

Completed results include Shannon counting, the De Morgan parity lower bound,
AC0 parity separation, monotone Boolean CLIQUE, monotone arithmetic clique
support bounds, Hessian rank, and Waring and rectangle bounds. Restricted
models and their charged operations are explicit in the theorem statements.
The AC0 development has a detailed [theory map](ac0-theory-map.md).

`Algebraic.LowerBound.Cutwidth` proves that a rectangle-free Boolean function
with polynomial rectangle threshold and at least `2 ^ (n - 2)` accepting inputs
needs more than `(4 - ε) n` gates over the full binary basis `B₂`, for every
`ε > 0` and all large `n`. The pathwidth bound `(1/6 + ξ) h` for simple cubic
graphs and the existence of such a hard family are explicit hypotheses of
`Cutwidth.eventually_lt_size_of_pathwidthBound`; the library adds no axioms.
The [cutwidth guide](cutwidth-lower-bound.md) describes the argument and
its hypotheses. Two corollaries share the assembly: the same bound for
nondeterministic circuits with at most `n` witness bits
(`Cutwidth.nondet_eventually_lt_size_of_pathwidthBound`), and an average-case
form for balanced functions, where circuits of size `(4 - ε) n` agree with the
function on at most `(1/2 + 3ν) 2 ^ n + 2 ^ ((1 - ε/24) n)` inputs
(`Cutwidth.eventually_card_agree_le_of_pathwidthBound`, see the
[average-case note](average-case-cutwidth.md)). `Algebraic.LowerBound.Nechiporuk` proves that the same
functions need `Ω(n² / log n)` leaves in any formula over the full binary
basis, by Nechiporuk's subfunction counting; rectangle-freeness gives the
maximal subfunction count on every block simultaneously. The
[Nechiporuk guide](nechiporuk-lower-bound.md) has the details.
`Algebraic.LowerBound.KarchmerWigderson` provides the communication-game
view of De Morgan formulas, the Karchmer–Wigderson theorem, the composition
`f ⋄ g` with its elementary depth and size bounds, and the
Karchmer–Raz–Wigderson conjecture, in depth and size forms with constant slack
for non-constant functions, as explicit propositions that are not proved; see
the [Karchmer–Wigderson guide](karchmer-wigderson.md).

`Algebraic.Basis.DeMorgan.ShannonLupanov` transfers CSLib's sharp bounds to
the local De Morgan complexity measures. The conversions preserve semantics,
remove identity gates when exporting to CSLib, and track the difference between
total gate count and weighted logical-gate cost. The local mass-production
constructions retain their explicit finite cost bounds.

The Fusion development is parameterized by the circuit signature,
interpretation, target problem, observation model, and operation costs. This
keeps the circuit-to-cover argument independent of its set-theoretic or
algebraic applications. A separate least-fixed-point model handles cyclic
circuits without weakening the acyclic invariant of `Program`.

The [application guide](applications.md) maps representative results to
their imports, models, and charged operations. Module docstrings and the
generated API reference give their full statements. The
[upstream preparation record](upstream-readiness.md) tracks the remaining
integration and review work.

The standalone repository's research notes (its library stocktake and the
preparatory noncommutative recurrence) were not imported; they remain in the
[algebraic-circuits repository](https://github.com/SamuelSchlesinger/algebraic-circuits).

## Build and checks

The library is part of Complexitylib's default target and root import, so the
repository-wide commands build and check it:

```sh
lake build --wfail
lake exe runLinter Complexitylib      # Mathlib/Batteries environment linters
lake env lean scripts/AxiomGuard.lean # axiom audit
python3 scripts/lint_style.py         # headers, module docs, imports, native_decide
```

`scripts/AxiomGuard.lean` checks that every declaration compiled from a
Complexitylib module, including every `Complexitylib.Algebraic.*` module and
the library's `Cslib.Circuits` extensions, depends only on `propext`,
`Classical.choice`, and `Quot.sound`; a declaration depending on `sorry` or
`native_decide` fails it. Its header documents its limits: it trusts the
compiled `.olean` files and cannot see `example`s.

`scripts/lint_style.py` checks the MIT header, module docstrings, import
reachability, and the `native_decide` ban for these files. The imported
library has a scoped exemption from its line-length and `_root_` checks until
the consolidation in `ROADMAP.md` (item 7).

The standalone repository's `lake test` suite (`AlgebraicTests`, with its own
axiom audit and executable `native_decide` tests), its `lake lint` driver, and
its import checker `scripts/check_imports.py` were not imported. Complexitylib's
executable regression modules (`Complexitylib.Classes.P.Cobham.Validation`,
`Complexitylib.Models.TuringMachine.SingleTape.Validation`,
`Complexitylib.Models.TuringMachine.Repetition.Validation`,
`Complexitylib.Circuits.Encoding.Validation`, and
`Complexitylib.SAT.Tseitin.Machine.Validation`, each built with
`lake build --wfail <module>`) cover other parts of Complexitylib; none covers
this library. The regression files that the guides cite by link live in the
[algebraic-circuits repository](https://github.com/SamuelSchlesinger/algebraic-circuits).

## Documentation

The API reference, including this library, is generated with
[doc-gen4](https://github.com/leanprover/doc-gen4) from Complexitylib's
`docbuild/` subproject:

```sh
cd docbuild && lake build Complexitylib:docs
```

CI publishes it at <https://samuelschlesinger.github.io/complexitylib/>. The
first documentation build also processes imported Mathlib modules and can
take substantially longer than later incremental builds.

## License

Algebraic is available under the
[MIT License](../../Complexitylib/Algebraic/LICENSE).

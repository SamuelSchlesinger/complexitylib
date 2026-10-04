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
- `import Complexitylib.Algebraic.LowerBound.Cutwidth` for the
  `(1 + π(3 + 2√2)/6 - ε) n ≈ (4.0517 - ε) n` lower bound over the full binary basis; see
  the [cutwidth guide](cutwidth-lower-bound.md);
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
family with `log₂ K(n) = o(n)` and at least `2 ^ (n - 2)` accepting inputs
needs more than `(4 - ε) n` gates over the full binary basis, for every
`ε > 0` and all large `n` (`Cutwidth.eventually_lt_size_of_rectangleFree`).
The sharp cubic bisection and pathwidth bounds are proved. Ordering the cubic
core by Gaussian distance-kernel scores improves the graph-ordering coefficient
from `1/3` to `(6/π)(3 - 2√2) ≈ 0.32768`, so the same families need more than
`(1 + π(3 + 2√2)/6 - ε) n ≈ (4.0517 - ε) n` gates
(`Cutwidth.eventually_lt_size_of_rectangleFree_gaussian`).

The graph proof uses boundary normalization, connected clusters, and red-edge
incidence counting to find bounded helpful sets. Lifting and reversing the
first normalization phase gives size at most `36 M (1 + 3 M)` when
`4 ≤ 3ξM`; accumulation and rebalancing prove the Monien–Preis bisection
conclusion. The Fomin–Høie reduction then gives cubic pathwidth. The
connected-cluster replacement for marked-tree reorganization was developed
in this formalization. The thin-path, weighted core, and restoration
infrastructure remains available independently.

`Cutwidth.Extractor` transfers flat-source sumset extraction to the
hard-family properties. Balanced padding permits any fixed error below
`1/2` at twice the threshold and preserves any supplied `FP` evaluator.
`Extractor.SourceReduction` proves that the specified low-order parity bounds
on sufficiently many good source fixings imply extraction with error `35/72`.
This includes normalized moment bounds, majority robustness, and averaging
over fixings. The finite extractor-to-sampler conversion, amplification,
and simultaneous parity-coordinate selection are also proved. The concrete
condenser polynomial map has checked degree and linearity invariants, plus
finite neighbor expansion and seed-preserving flat lossless condensation
for a supplied irreducible modulus. Exact subset averaging extends the
guarantee to all larger flat supports. An explicit binary trinomial family
has checked irreducibility, quotient cardinality, a noncube root, and a
fixed-width coefficient codec. Addition, multiplication, remainder, bounded
modular squaring, blockwise Horner evaluation, and trinomial generation have
uniform `FP` evaluators. The complete encoded condenser uses checked
extension-field packing and computes exactly the polynomial map, with
injective source encoding at every fixed length within capacity and
source linearity for each seed. Its flat-source and mixture guarantees now
apply to the actual program. An explicit unary parameter schedule proves
error at most `2^-e`, seed width at most `6(u+1)T`, and output width at most
`(1+1/u)k+b`, where `T=e+clog₂(9(n+1)(k+1))+1`, `b` is the seed width,
and `u>0`. A single `FP` evaluator includes this parameter generation.
The next checked layer is a concrete one-shot strong linear extractor.
`Extractor.Strong` tests the joint seed-output distribution; `Hashing` proves
the sharp finite leftover-hash bound, and multiplication followed by a
coefficient prefix supplies a universal linear hash with a uniform `FP`
evaluator. Exact coordinate serialization and mixture-aware composition
connect this hash to the scheduled condenser. For every flat `n`-bit support
of size at least `2^(ell+2e)`, `decodedOneShotExtractor_flat` gives `ell` output
bits and error at most `2^-e`, retaining both independent seeds. The actual
program has exact output length, preserves source XOR for fixed seeds, and
has one uniform `FP` evaluator including parameter generation.

The same guarantee now holds for every normalized source with point masses
at most `2^(-(ell+2e))`. An exact decomposition into flat supports uses
Mathlib's Birkhoff--von Neumann theorem, formalized by Bhavik Mehta. The
scheduled condenser likewise preserves the cap `2^-k` on a seedwise ideal
output with error `2^-e`. Finite coupling, marginal replacement, two-block
repair, and a general block-source invariant are also checked. These supply
the probability layers needed when intermediate conditional sources are
nonuniform. Shared-seed block condensation is now proved as well: applying
the same strong condenser to `t` dependent blocks with one uniform seed
gives a seed-conditioned block source with joint error at most `t*δ`, where
`δ` is the condenser error. The result specializes to the actual scheduled
condenser and to strong block extraction against uniform joint output.
Multiblock splitting is also checked: a threshold-`2^k` block source on `t`
pairs has a split law within distance `t*2^-e` of a threshold-`2^s` source
on `2t` successive half-blocks, when each half has `2^m` values, `s≤m`,
and `m+s+e≤k`.
The pairs can be dependent, and splitting uses no new randomness.
A seed-family corollary retains earlier seeds with the same joint error.

The finite recursive composition is now defined and checked. Each level
adds one fresh seed, applies a shared-seed condenser, and splits its pair
outputs. The proof carries the joint approximation through all levels;
it does not assume a small error at every individual seed. Joining an
initial condenser and a final block extractor gives an actual strong
extractor from supplied components satisfying the finite entropy budgets.
For `h` levels with local error `2^-E`, its total error is at most
`(3*2^h-1)*2^-E`; `E=e+h+2` suffices for error `2^-e`. Seed cardinalities
multiply once per level, so power-of-two seed widths add.
The recursive maps preserve fixed-seed additivity when their components do.
The actual scheduled condenser now has a checked representation as two equal
Boolean-vector halves. Its output length is even, so this representation
preserves the entropy threshold, error, and rate without padding.
An explicit sufficient inequality now supplies a level's two entropy
conditions. The actual shared-seed block-level program also has a uniform
`FP` certificate and exact fixed-width tuple semantics.
Its output is proved equal to the statistical condense-and-split map.
The scheduled extractor now instantiates every component at actual rounded
widths. It uses a factor-four entropy recurrence and an explicit leaf reserve;
its strong guarantee, fixed-seed XOR law, and finite total seed bound are checked.

The asymptotic family fixes natural `a,e`, takes `L=clog 2 (n+1)` and
`h=a*clog 2 (L+1)`, and eventually extracts with error at most `2^-e`.
Its actual entropy threshold in bits is `o(n)`, its actual seed length is
eventually at most `16384L`, and its output lies between `L^(a+1)` and
`2^a*(L+1)^(a+1)`. Thus the shared-seed recursion supplies any fixed
polylogarithmic output power with logarithmic seed length. These bounds
are proved for the rounded construction, with `a,e` fixed before the limit.

One total `FP` evaluator now generates all parameters, runs the initial
condenser and every block level, and extracts the leaves. It clips a runtime
requested depth to `L`; the family's requested depth is eventually unchanged.
The independent bound `4^depth≤4*(n+1)^2` certifies parameter generation
even on inputs that cannot meet the statistical entropy premise. A canonical
seed codec identifies the full field-seed tuple with every word of the exact
seed length, without enumeration. On those words, the complete program
computes exactly the statistical extractor's output, serialized in block order.
For each fixed `a,e`, `polylogBlockExtractorProgram` is one `FP` string
function of the source and seed word, with proved eventual agreement with
the entire family on every source input and canonical seed.
The Boolean interface reads the actual program's output and proves strong
extraction with the complete uniformly sampled Boolean seed, together with
fixed-seed XOR linearity. It requires no caller-supplied field instances.

This follows the condense-then-hash and recursive steps of
[Chattopadhyay--Goodman--Liao, Lemma 4.9 and Theorem 5.6](https://eccc.weizmann.ac.il/report/2021/075/download/),
with a coarser entropy schedule than CGL's theorem. A separate near-halving
schedule now supplies the ordinary extractor `Γ`: for all sufficiently large
`b`, it takes `8b` source bits with entropy at least `2b`, returns `b` bits
with error at most `1/4`, and uses at most `2^27*(clog 2 (b+1))^3` seed bits.
The finite guard and every rounded reserve inequality are proved for the
actual construction. Its complete bit program has exact semantic correctness,
including arbitrary trailing seed bits. Padding to the displayed budget
preserves the strong guarantee with the whole seed retained.
`gammaBlockExtractorEval` is one total `FP` string function, and its exact
all-size output agrees with `gammaBlockPaddedExtractor` on the displayed
seed budget. The extraction guarantee uses the proved eventual size guard.

The actual common-scale extractor calls now support a complete advice-bit
step and advice fold with a total `FP` evaluator. The finite probability
proof covers the weak phase before advice differs, both orientations of
the first unequal bit, and preservation afterward. Its exact transcript
induction tracks the executed programs, normalized factors of the original
sources, and source-envelope growth `D^(8i)` and `C^(5i)`. Once advice has
differed, the transcript fixes the tampered current state; the stronger
step estimates retain that state and the full original left state. No
intermediate uniformity guarantee is supplied by the caller.
`adviceCorrelationBreaker_dist_le` completes the actual strong-output
theorem: for normalized conditionally independent source factors, a
conditionally uniform honest right input, and the stated average left
mass bound, unequal fixed advice words of equal length give a nearly
uniform honest output retaining the original tag, entire original right
state, and actual tampered output. The dyadic corollary proves error at
most `2^-target` from its explicit finite entropy reserves.

This follows [Chattopadhyay--Goyal--Li, Algorithm 2 and Lemma 6.9](https://arxiv.org/pdf/1505.00107).
The implemented program also performs one final depth-24 extraction from
the original left source. The checked finite accounting conservatively
amplifies errors by `4^a` across `a` advice bits. The explicit choices
`e=target+2a+clog 2 (a+1)+10`,
`L=1024*(a+target+out+clog 2 (n+1)+256)`, and
`m=2^150*(a+1)*L` satisfy the actual program guards and all entropy reserves.
Nonvacuous use still requires `m≤n` and a source meeting the stated mass bound.
Output truncation preserves the strong guarantee at any requested width
within the final output, retaining the truncated tampered output.
The selected-parameter theorem combines these pieces into an actual
`out`-bit program guarantee with error `2^-target`, assuming only the
normalized factored source, uniform honest right input, left mass bound,
and fixed unequal advice words of length `a`. All finite guards and
reserve inequalities are discharged by the chooser.
These conservative constants are our deductions; they do not reproduce
the paper's sharper parameter bounds.

`Advice.Extraction.Program` now computes the chooser, normalizes the right
word by taking its selected prefix with false completion, and returns the
requested output in one total `FP` evaluator. Its exact canonical agreement
uses no entropy or statistical premise. `Advice.Extraction.Perturbed`
allows an honest right input jointly within `ρ` of uniform given the tag
and adds only `ρ` to the error: repair preserves the original right state
and actual tampered output exactly. `Advice.Extraction.Alternating` then
handles the source/seed role reversal after observing a right-side message,
charging its alphabet size to the source envelope.

The complete pairwise first phase of the
[Chattopadhyay–Liao conversion, Theorem 6.1](https://arxiv.org/html/2110.12652v1#S6)
is now proved for the actual linear extractor, advice program, and final
linear extraction. It starts from the original normalized factors, a
uniform honest right input, the left mass envelope, and unequal advice.
The actual output is close to uniform while retaining the complete
executed transcript, original right state, and one tampered output.
The original-left contributions satisfy the same bound, and explicit
finite source reserves give any dyadic error target. Exact transcript
factors and envelope totals include normalized null rows.
The first-phase chooser now discharges every numerical component guard
and reserve, with total polynomial-time generation of all chosen values.
The selected theorem gives error `2^-target` from the original source
hypotheses and its chosen mass bound; the source still must meet that
entropy requirement.
`Matched.Growing` proves statistical bounds at variable depth under an
explicit finite seed budget, and `Matched.Affine` retains
the entire correlated mask state. `Matched.Growing.Program` now supplies
one total polynomial-time evaluator at depth `clog₂(t+1)+64`, including
all parameter generation and exact agreement on canonical inputs.
`PhaseOne.Program` composes all three actual calls into a total polynomial-time
evaluator, with exact canonical agreement under their finite component guards.
Its selected wrapper computes every chooser value and normalizes the right
word, so its canonical agreement has no numerical or statistical premise.
`Merging.Smooth` constructs the conditional repair needed for the next
stage, preserving original observations and charging the old distance once.

The complete affine conversion, actual amplified sampler, fixed-family parity
tests, and majority composition are proved. The actual source entropy is
sublinear, both sampler guards hold eventually, and bounded enumeration
supplies one uniform polynomial-time evaluator at every input length.
`Cutwidth.sourceReductionHardFamily_eventually_lt_size_gaussian` proves the
unconditional `(1 + π(3 + 2√2)/6 - ε) n ≈ (4.0517 - ε) n` lower bound for this
fixed concrete family over the full binary basis;
`Cutwidth.sourceReductionHardFamily_eventually_lt_size` keeps the
coefficient-four case. The bound uses its full input length, and
`Extractor.sourceReductionHardLanguage_mem_P` proves the language is in `P`.
The [cutwidth guide](cutwidth-lower-bound.md) records the exact theorem,
parameter guarantees, and source credits.

The same lower bound holds for nondeterministic circuits with arbitrarily
many witness bits (`Cutwidth.nondet_eventually_lt_size_of_rectangleFree`).
For balanced functions with polynomial threshold, circuits of size
`(4 - ε) n` agree on at most `(1/2 + 3ν) 2 ^ n + 2 ^ ((1 - ε/24) n)` inputs
(`Cutwidth.eventually_card_agree_le_of_balanced`; see the
[average-case note](average-case-cutwidth.md)).
`Algebraic.LowerBound.Nechiporuk` proves that the same rectangle-free
functions need `Ω(n² / log n)` leaves in any formula over the full binary
basis. The [Nechiporuk guide](nechiporuk-lower-bound.md) has the details.
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

# Complexitylib roadmap

The mathematical map of the library now lives in the
[blueprint](https://samuelschlesinger.github.io/complexitylib/blueprint/)
(sources in [`blueprint/`](blueprint/)). It lists every headline result and
planned theorem with its Lean declaration, its status, and its dependencies;
its dependency graph shows which planned results are ready to work on.

This document covers what the blueprint does not: how to prove things in this
library, the infrastructure priorities, and how to contribute. The previous
long-form roadmap, with detailed progress logs, is preserved in git history
(`git show f47e3c1:ROADMAP.md`).

## Principles

1. **State the exact variant.** Resource conventions, uniformity, error
   constants, zero-length inputs, promise behavior, and encodings belong in
   the theorem statement or right next to it.
2. **Auditable statements, checked proofs.** Definitions and public theorem
   statements stay short enough to audit; proof machinery lives in `Internal`
   modules.
3. **Prove through characterizations before building machines.** Most
   class-level results follow from the levers below. Build a bespoke machine
   only when the exact bound is the point of the theorem (hierarchies,
   universal-simulation overhead, linear-time examples).
4. **No silent hypotheses.** A result that needs an unproved assumption is
   stated as the implication. A hypothesis that is a true theorem is proved,
   not carried; an interface predicate that a theorem assumes should have at
   least one instance in the library.
5. **Concrete bound first, asymptotics second.** Constructions expose an exact
   resource bound and derive the `BigO` statement from it.
6. **Finite counting before probability theory.** Exact counting over
   `Fin T → Bool` is easier to compute with and audit.
7. **Honest representations.** Parsing, malformed inputs, output length, and
   conversions between `List Bool` and `Fin n → Bool` are explicit.
8. **Judge abstractions by their payoff across the library.** A compiler or
   characterization theorem pays a large fixed cost once; measuring it against
   a single consumer undervalues it. Cobham's theorem is the example to follow.
9. **Small steps.** A contribution adds one definition, one lemma family, or
   one theorem layer and leaves every gate green.

## Levers

Check these before constructing a Turing machine.

| Goal | Lever | Where |
| --- | --- | --- |
| `f ∈ FP` | Cobham's algebra and the closure rules built on it; `iterate_mem_FP` and its variants for polynomially many iterations of a step, `recFold_mem_FP_of_bound` for a bitwise fold with short states; `catRange_mem_FP` for concatenating a rule's outputs over a unary range, with corollaries for list encodings, counts, bounded search, maxima and bitwise descriptions; for a function to `ℕ` (written in unary) or a test, the `UnaryFn`/`FPPred` rules: arithmetic, comparisons, connectives, case distinction, bounded sums, counts, search and maxima, loops on numbers, division, capped powers and logarithms, bounded quantifiers (`FPPred.forall_lt`, `FPPred.exists_lt`); `mem_FP_of_bounded_key` and `FPPred.of_bounded_key` for anything that depends on a key of bounded length; `toBitsLE_mem_FP`, `bits_mem_FP` and `UnaryFn.fromBitsLE_min` between unary and binary; `encodeList_mem_FP`, `natEncode_mem_FP` for writing a `DataEncode` encoding | `Classes/P/Cobham.lean`, `Classes/P/Iterate.lean`, `Classes/P/Range.lean`, `Classes/P/Unary.lean`, `Classes/P/BoundedQuant.lean`, `Classes/P/FinsetDomain.lean`, `Classes/P/NatCodes.lean`, `Classes/P/DataEncode.lean`, `Classes/Containments/Internal/FPBridge.lean` (re-exported with `polyRuler`, `emptyFlag`, `dropOne` by `Classes/P/Bridge.lean`), `Classes/P/Cobham/Internal.lean` |
| `L ∈ P` | `mem_P_of_decisionFn`, `FPPred.mem_P`, `mem_P_of_bounded_key`, `mem_P_preimage`, `P_compl`, `P_inter`, `P_union` | `Classes/P/DecisionFn.lean`, `Classes/P/Preimage.lean`, `Classes/Containments.lean` |
| `L ∈ NP` | `NP.mem_NP_of_FNP`, `NP.mem_NP_of_linear_witness`, `mem_NP_of_poly_witness` (polynomial-time verifier, bounded witnesses) | `Classes/NP/WitnessConstruction.lean`, `Classes/NP/Verifier.lean` |
| `L ∈ PSPACE` | `mem_PSPACE_of_iterate` (exponentially many iterations of an `FP` step on a polynomial-size state), `mem_PSPACE_of_bitstring_fold` (ordered fold over every fixed-width bitstring, with short prefix accumulators), `PSPACE_compl` | `Classes/Space/Iterate.lean`, `Classes/Space/BitstringFold.lean`, `Classes/Containments/Internal/ComplementSpace.lean` |
| universal simulation | `TM.utmTM_simulates_pair` | `Models/TuringMachine/UTM/Universality.lean` |
| closure under reductions | `MapReducesPoly.mem_P`, `MapReducesPoly.mem_NP`, `mem_NP_preimage` | `Classes/NP/Reduction.lean`, `Classes/NP/Closure.lean` |

Some of these levers still live in `Internal` modules; promoting them to
stable surface modules is part of priority 2 below.

The public verifier entry point is `Complexitylib.Classes.NP.Verifier`; linear-only
clients can use `Complexitylib.Classes.NP.Verifier.Linear` to avoid polynomial
padding dependencies. See the
[public-only regression examples](scripts/VerifierApiCheck.lean) for linear and
polynomial witness bounds, including the zero bound. SAT, exact-3SAT, CircuitSAT,
and its extension language all use this route. Exact theorems about the original
`SAT.satGuessVerifyNTM` remain in the separate `Complexitylib.SAT.GuessVerify`
compatibility API. The old `Classes.NP.Internal.GuessVerify` import still works
as a compatibility shim, but imports SAT; new membership clients should use the
neutral public entry point.

## Priorities

In order. Each item says why it matters and roughly how large it is.

1. **Guard against vacuous and silent hypotheses.**
   - Add two audits to CI, each with an allowlist of famous open problems and
     clearly named conditional theorems. The first flags theorem hypotheses
     that are closed propositions, the shape of an unproved assumption. The
     second flags predicates that public theorems assume but the library never
     establishes. Pair the second with a non-vacuity rule: every interface
     predicate a public theorem assumes has at least one instance. That rule
     would have caught the unsatisfiable hypotheses that made the
     symmetry-of-information collapse theorems vacuous until September 2026
     (a pair-composition contract demanding finite zero-step complexities, an
     estimator required to be correct at every clock, and a finiteness field
     inside `TimeBoundedSymmetryOfInformation` that no machine can meet).
   - Instantiate the remaining uninstantiated interfaces: a universal oracle
     machine for `OracleTM.IsEfficientlyUniversal`, and a list-decodable code
     family for the Nisan–Wigderson reconstruction.
2. **Reroute through characterizations and delete superseded machines.**
   `SAT ∈ NP` (about 12k lines of bespoke verifier and guess-and-verify
   machines), the Cook–Levin emitter (about 6.7k), the Tseitin transducer
   (about 6k), `PP ⊆ PSPACE` and `PH ⊆ PSPACE` (about 10k, bespoke machines),
   and the concrete languages can each be re-proved in a few hundred lines
   with the levers above, including concatenation over a range
   (`catRange_mem_FP`), plus one new `FP` combinator, a streaming finite-state
   fold. Keep public statements; replace proofs.
3. **One polynomial-space game-tree theorem.** Evaluating a
   polynomial-depth, exponentially branching game tree is in `PSPACE`.
   Savitch, `IP ⊆ PSPACE`, `PH ⊆ PSPACE`, `PP ⊆ PSPACE`, and `TQBF ∈ PSPACE`
   become instances, and the frame and stack encodings that Savitch and
   `IP ⊆ PSPACE` each hand-roll disappear.
   The depth-one ordered fold is available as
   `SpaceIter.mem_PSPACE_of_bitstring_fold`, with canonical fixed-width
   enumeration and an explicit bound on every prefix accumulator. The
   polynomial-depth stack evaluator remains to be built.
4. **A logarithmic-space programming layer.** The library has no closure of
   `FL` under composition and no way to write log-space algorithms without
   hand-allocating registers; the logspace-uniform circuit generator costs
   about 50k lines for a 2k-line program, and `NL = coNL` is stalled on the
   same problem. Needed: `FL` closed under composition; a compiled loop
   language over O(1) registers of O(log n) bits with one correctness theorem;
   and a circuit encoding whose gate references are affine in loop counters.
5. **Proof automation.** `Complexitylib.Tactic.PolyTime` adapts the CSLib
   crypto branch's `polytime` approach to `FP`, `UnaryFn`, and `FPPred`:
   registered closure rules, local algorithm certificates, and bounded
   iteration. The PCP development uses it throughout arithmetic, parsers,
   verifier construction, and expander graph algorithms. Register reusable
   certificates with `@[polytime]`; use `polytime [program]` to unfold a
   program and compose its certificates. General loops still need explicit
   state-size invariants. Add automation for `PolyBound`, and try `grind`
   on frame, `Function.update`, and index goals.
6. **Consolidate duplicated representations.** About 24 modules define their
   own codecs, about 25 define their own probability notions (Mathlib's
   `Finset.expect` and `Finset.dens` cover them), circuits and formulas have
   about 14 parallel representations with 22 bridges, and binary counters
   exist in about 8 versions. One codec interface, one probability
   convention, and one formula type with substitution would absorb most of
   them.
7. **Move every circuit development to CSLib's circuit model.** CSLib's
   straight-line programs over a signature (`Cslib.Circuits`) become the only
   semantic circuit type, and our typed `Circuit` is retired. Nothing depends
   on the typed representation mathematically. Each of our bases is one CSLib
   signature whose operation symbols are our gates: an operation, a fan-in,
   and a negation pattern. Unbounded fan-in and threshold bases are signatures
   with infinitely many operations. Our free negations are therefore
   reproduced exactly. Counted output gates are reproduced exactly on
   single-output circuits whose output is an internal gate
   (`Circuit.GatedOutputs`). With several outputs they are not: a gated CSLib
   circuit may point two outputs at one gate, or feed an output gate into
   later gates, while typed outputs are distinct sink gates, so the planned
   converse translation gives only the bounds
   CSLib size ≤ typed size ≤ CSLib size + M − 1. Every size class is
   single-output. `NeZero N` and
   `CircuitFamily.emptyOutput` stay: the fan-in-two AND/OR basis has no
   constants, so it has no zero-input circuits. The algebraic-circuits
   library, imported wholesale as `Complexitylib/Algebraic` (done, September
   2026), already works in this model. The detailed plan for phases 2 and 3
   is `docs/CircuitMigration.md`.

   The migration targets upstream CSLib's circuit API, which now includes the
   author's merged circuit work: bundled gate counts (#949), sequential and
   parallel composition (#952), complexity on a support (#955), inductive
   wires (#957), and language slices (#954). The CSLib circuit modules that
   are not upstream (relative complexity, circuit families with `SIZE` and
   `P/poly`, completeness of the De Morgan basis, circuit dependencies) are
   carried in `Complexitylib/Cslib` under their CSLib namespaces; counting via
   involutions (#950) and Redkin's exact parity complexity `4(n - 1)` are not
   in the build. CSLib's `SIZE` and `PPoly` (De Morgan, as in Arora and
   Barak) then become the reference classes. Each phase lands with public
   statements unchanged:
   1. **Signatures and the correspondence.** `Basis.signature` and
      `Basis.interpretation` for every basis (done), and translations between
      typed circuits and straight-line programs over them. The forward
      translation `Circuit.toStraightLine`
      (`Complexitylib/Circuits/StraightLine.lean`) is done: it computes the
      same function (`eval_toStraightLine`), has the same size
      (`size_toStraightLine`), has gated outputs
      (`gatedOutputs_toStraightLine`), and has the same total fan-in
      (`totalFanIn_toStraightLine`). So far the correspondence runs one way,
      from typed circuits to CSLib's. The converse translation, from gated
      CSLib circuits, with depth and the round trip, is next.
   2. **Redefine the measures and classes** (`sizeComplexity`, `SIZE`, `PPoly`,
      `CircuitFamily`, `DEPTH`, `NC`, `AC`, `TC`) over CSLib circuits, keeping
      their names, and re-prove the old statements through the correspondence.
   3. **Port the consumers by area**, replacing or retiring proofs:
      - Counting and gate elimination: Shannon's and Schnorr's bounds follow
        from CSLib's counting and algebraic-circuits' `3(n - 1)` parity bound,
        and the essential-input bound from `Circuit.essential_le_size`. The
        `3(N - 1)` bound for `Basis.andOr2` circuits is already derived through
        the algebraic library (`parity_size_ge_three_mul`); only the `2N - 1`
        `CircDesc` proof remains to retire, after which the internal counting
        model (`CircDesc`) is deleted.
      - Builders (composition, hardwiring, projections, reindexing,
        multiplexer, majority, about 12.7k lines of `Fin (N + G)` offset
        arithmetic) become algebraic-circuits' substitution, restriction, and
        translation, plus CSLib's synthesis calculus.
      - AC⁰: parity ∉ AC⁰ for our classes is proved (`xorBool_not_mem_AC0`)
        from the library's own normalization and switching internals.
        Reconcile them with algebraic-circuits' Håstad development and retire
        whichever is superseded. Strict majority ∉ AC⁰ (`majority_not_mem_AC0`)
        follows from the top-down gate bound, and `not_TC0_subset_AC0Mod_three`
        from Razborov–Smolensky.
      - NC¹: port the circuit-to-formula unfolding used by
        `NC1_subset_Width5BP`.
      - MCSP and the other consumers of `sizeComplexity` and composition.
      - `RawCircuit` stays as the serialization format that machines read and
        write. It is already a straight-line program, so only its round trip
        is retargeted, and the roughly 60k lines behind `P ⊆ P/poly`,
        `BPP ⊆ P/poly`, uniform `P/poly`, and circuit satisfiability keep their
        machine proofs.
   4. **Delete the typed `Circuit`** and every superseded internal, and unify
      the formula types (`BoolFormula`, `AC0Formula`, `MonotoneFormula`, and
      algebraic-circuits' formula and expression types) behind one type with
      substitution, as item 6 asks.
   5. **Converge and upstream.** Gather the declarations that extend CSLib
      types into `Complexitylib/Cslib` like `Complexitylib/Mathlib`, retire
      the algebraic-circuits style exemption, and upstream reusable pieces
      (families, costs, depth, synthesis extensions, the `Interop/Cslib`
      lemmas) to CSLib.
8. **A friendlier machine-authoring layer.** For work that must stay at the
   Turing-machine level (hierarchies, universal simulation, single-tape
   simulation), several model conventions cost proof effort on every step:
   sequential composition spends a real step at each seam, branches read their
   result back from the output tape, heads reading the left marker must move
   right, idle tapes must be rewritten, and deterministic and nondeterministic
   execution duplicate their theory. An authoring layer without these costs,
   compiled once into the canonical machine, would remove them without
   changing any class definition. Evaluate it on one real consumer first.
9. **Decide the fate of the RAM development.** `RAM.P = P` is proved, but
   nothing outside the RAM tree uses it. Either give it consumers or archive
   the parts that duplicate other routes.

## Core API and proof engineering

The standing infrastructure track: shared tape, run, encoding, and asymptotic
facts in stable public modules so later work does not duplicate local lemmas.
Design history for machine authoring (the rose-tree machine evaluation, the
structured RAM frontend, the binary routine experiments, and the
cross-construction audit) is in [`docs/N0-MachineAuthoring.md`](docs/N0-MachineAuthoring.md).

Open:

- [ ] A canonical extensionality and simplification API for `Tape`, `Cfg`,
  `Tape.init`, `Γ.ofBool`, `TM.reachesIn`, and `NTM.trace`.
- [ ] Consolidate the repeated endpoint-determinism, run-concatenation,
  halting, and time-bound monotonicity lemmas.
- [ ] Give every major construction a named concrete time and space bound and
  a separate `BigO` theorem.
- [ ] Audit aggregation modules so public imports never name proof-only
  implementation files.
- [ ] Standardize the low-level contracts larger abstractions compose from:
  tape-shape predicates, explicit preservation frames, appendable endpoints,
  and exact-time sequential and loop rules. Treat a machine whose proof
  interface is destructive or underspecified as an API defect.
- [ ] Test the named-tape endpoint vocabulary (`TM.Experimental.EmitSpec`) on a
  construction independent of the two Tseitin pipelines where it already
  helps, then decide whether to promote it.
- [ ] Inventory the repeated controller mechanics in the universal machine,
  repetition, and Tseitin developments, and extract one small child-call and
  routing layer if the inventory justifies it.
- [ ] Add the remaining narrowly oriented projection lemmas for `write`,
  `move`, and `writeAndMove`, and migrate older modules to the shared
  initialized-tape and Boolean-symbol lemmas.
- [ ] Refresh module documentation that still describes completed proofs as
  skeletons.

Formalization hazard: broad `[simp]` attributes make machine-step goals explode
or loop. Prefer projection lemmas and narrowly oriented rewrite rules to marking
transition definitions `[simp]`. Moving a theorem must keep its public name or
leave a compatibility alias.

## Top-down parity and majority lower bounds

The track for Oliver Korten's *Top-Down Lower Bounds for All Depths* (ECCC
TR26-221, 2026) completes Theorem 3. `BooleanAnalysis.HarmonicMean` proves the
variational formula, all three transform properties, and the biased-cube
inequality (Lemmas 11--12 and Corollary 1). `BooleanAnalysis.Bernoulli` proves
downward-family transference, and `BooleanAnalysis.LightPatterns` completes
Lemma 10 with its exact constants and count of low-probability patterns.
The mass-to-density bridge is checked, including zero masses and rate zero.
`BooleanAnalysis.Fibers` proves the conditional-fiber entropy bound (Lemma 4),
the `63/64` good-fiber estimate, and the uniform-mass deficit bridge.
`BooleanAnalysis.CoordinateSampling` proves the conditional law for the two
sampled coordinate sets. Lemma 10 now applies to arbitrary finite coordinate
types, and `BooleanAnalysis.MirrorSets` proves `improved_mirror_set`, completing the
improved mirror step with `q = 32768*k*p`, reverse limit deficit `194*k`,
and mirror deficit at most `2*k+2`. `Circuits.KarchmerWigderson.Rounds`
defines general protocols with bounded message alphabets and at most `d`
rounds. `Circuits.KarchmerWigderson.TopDown` proves the rectangle adversary,
bilateral parity initialization, explicit finite obstruction, and
`parity_communication_lower_bound` with exponent `1/(d-1)`.
The circuit-to-protocol translation gives `Circuit.parity_wire_lower_bound`
for unbounded AND/OR circuits with free input negations and the existing
`totalFanIn` wire count. `Circuit.exists_roundProtocol_of_gates` gives the same
translation with an alphabet of size `2 * (n + g)` (a wire and its negation
flag), which yields `Circuit.parity_gate_size_lower_bound` and, at every fixed
depth, `Circuit.parity_superpolynomial_gates`. The source-to-declaration map,
model conventions, and explicit constants are in
[`docs/TopDownLowerBounds.md`](docs/TopDownLowerBounds.md).

`Circuits.KarchmerWigderson.TopDown.Majority` extends this argument to strict
majority, including even input lengths with ties false. The two adjacent
Hamming layers have logarithmic deficit and at least half their coordinates
lead to the other layer by a single-bit flip. Sparse sampling gives bilateral
density limits, so the generalized first-message argument retains the
`1/(d-1)` exponent. The checked `majority_communication_lower_bound`,
`Circuit.majority_wire_lower_bound`, `Circuit.majority_gate_size_lower_bound`,
and `Circuit.majority_superpolynomial_gates` use the same protocol and circuit
models as the parity result; the last gives `majority_not_mem_AC0`. This is an
extension of Korten's method; his Theorem 3 states the parity case.

## Seeded extractor improvements

Follow-ups to the recursive construction of
[Chattopadhyay, Goodman, and Liao](https://eccc.weizmann.ac.il/report/2021/075/).
The [cutwidth guide](docs/algebraic/cutwidth-lower-bound.md) records the
current component guarantees and remaining hard-family obligations.
Prioritize sharper entropy statements and finite constants before replacing
the construction. The unchecked items below are proof and API targets.

- [ ] **Expose the stronger entropy guarantee.** The generic near-halving
  theorem `nearHalvingBlockOutputBits_lower` already proves that the full
  output has at least `7/8` of the scheduled input entropy threshold. Expose
  that guarantee alongside the Gamma specialization, which advertises `b`
  output bits at entropy `2b`. Prove finite bounds for its actual threshold
  `gammaBlockInputEntropy b`, then formalize
  `gammaBlockInputEntropy b / b → 9/8` with real-valued division. This limit
  is a deduction from the rounded formulas, not yet a checked theorem.
  Keep the full output length and the truncated Gamma output distinct.
- [ ] **Tighten field rounding and propagate the constants.** Prove the
  candidate improvement
  `sparseFieldBits u T ≤ 3 * ((u + 1) * T)` for `0 < T`, replacing the
  current factor-six estimate by comparing with the preceding point of
  the `2 * 3^s` grid. Recalculate the one-shot seed bound, recursive reserve,
  depth offset, and padded seed budget where this improves them. Preserve
  explicit finite validity conditions and zero-input behavior; reductions
  to the current `2^27` seed coefficient must follow checked bounds.
- [ ] **Provide a general extractor interface.** Expose input length,
  entropy threshold, output length, and error independently, using integer
  `e` for error `2^(-e)`. Build on `nearHalvingBlockExtractor_dyadic`, which
  already permits variable error, instead of requiring callers to use the
  `8b, 2b, b, 1/4` specialization. State the valid finite parameter range,
  retained-seed guarantee, exact seed width, and uniform `FP` evaluator
  together; preserve the Gamma interface as a convenient instance.
- [ ] **Reduce seed length through a different construction.** First
  formalize the present schedule's obstruction: with depth `h`, rate
  `u = 16*(h+1)`, and local exponent `E = h+4`, its internal seeds alone
  use at least `h * (u+1) * (h+5)` bits. Since `h` grows like `log b`,
  improving constants alone cannot remove the cubic-logarithmic cost.
  Investigate a different recursion or condenser/extractor ingredient for
  quadratic or logarithmic seed length. The ordinary-extractor benchmark
  is [Guruswami–Umans–Vadhan, Theorem 5.12](https://salil.seas.harvard.edu/sites/g/files/omnuum4266/files/salil/files/acm2009.pdf):
  at these constant-rate, constant-error parameters, `O(log b)` seed bits
  suffice. Track retained-seed strength and fixed-seed linearity separately;
  a replacement must preserve whichever properties its consumers require.

## Cutwidth coefficient improvements

The circuit coefficient is `1 + 1/A` for any graph-ordering coefficient `A > 0`
(`eventually_lt_size_of_orderingBound`); a cubic cutwidth or pathwidth
coefficient `c` gives `A = 2c` (`eventually_lt_size_of_cutwidthBound`,
`eventually_lt_size_of_pathwidthCoefficient`). The Gaussian distance-kernel layout
proves the cutwidth coefficient `c = (3/π)(3 - 2√2)`, and the Gaussian edge-score
decomposition proves the pathwidth coefficient `p = (3/(2π)) arccos ((1 + 2√2)/4) ≈ 0.14035`,
so the explicit family needs more than
`(1 + π/(3 arccos((1 + 2√2)/4)) - ε) n ≈ (4.5625 - ε) n` gates
(`sourceReductionHardFamily_eventually_lt_size_gaussian`). The unchecked items below
are unreviewed proof candidates. Each must prove its graph lemma for every large cubic
graph, controlling all prefixes of one ordering simultaneously, before its constant
is used; until then it enters only through the conditional coefficient theorems.
Keep the threshold hypothesis `log₂ K = o(n)`; better extractor entropy does not
change the leading coefficient. Rectangle peeling extends the bound to the
average case without improving it, and neither the prefix-halving gain of AVOID
nor affine-aware counting is known to add to it.

The frontier method (`Complexity.Frontier`, from the-frontier-method `373e009`) restates
this argument in general form: circuits over any finite alphabet, any basis, and any
accepting set, with fan-in `r`, counting only gates of positive arity against the cycle
rank under the layout hypothesis `LayoutBound (r + 1) A`. `LayoutBound.of_orderingBound`
transfers the Gaussian ordering bound, so the explicit family needs more than
`(4.5625 - ε) n` gates of positive arity over every Boolean basis with constants free,
and `(r - 1) s > (1 + 1/A_(r+1) - ε) n` for every fan-in `r` from Gaussian vertex layouts
in degree `d`, with `A_d = 3d/(2d - 3) · arccos(2√(d - 1)/d)/π < 3/4` and `A_4 = 2/5`, so
`(7/4 - ε) n` gates at fan-in three (`Frontier.sourceReductionHardFamily_lt_innerSize_gaussian`,
`..._degree`, `..._fanInThree`). The mirror is refreshed by `scripts/sync_frontier.py`; it
keeps upstream's degree-generic Gaussian proof alongside the cubic one here, and
`Frontier.gaussianCoefficient_eq_frontierCoefficient` checks that the binary coefficients
agree. Weighted
peeling gives the average case at the same coefficient; the explicit extractor, with
error `35/72`, agrees with every such circuit on at most a `71/72 + 2^(-γ n)` fraction
(`Frontier.sourceReductionFamily_agreement_le`). The development also checks signal
hypergraph cuts and their submodularity, exact linear syndrome counts, transition codes,
pruning, distribution-sensitive transition masses and fractional moments, trees of
regions, decomposable union/product DAGs, additive generators with sumset-free thresholds
and joint linear information, mixed input-output fibers and MDS maps, monoid
ledgers, linear maps with dual-number linearization, polynomially small average-case
advantage from polynomially small extractor error, and independent median updates; the
[research note](research/circuit-lower-bound-frontiers/frontier-method/index.md) records
what each refinement still needs.

The cut-counting lemma now charges a vertex by the bit patterns that satisfying
assignments realize on its charged edges (`Network.card_accepting_le_of_realized`,
with `Network.realized`, `Network.Determines`, and `Network.charged`); counting
every edge, `2 ^ (w + 3)`, is the special case `Network.card_accepting_le`. In the
wiring network one edge per *generator* determines a cut, where a carried signal
is a generator unless it is a gate both of whose argument signals are carried by
the same cut, so `Wiring.card_accepting_le_of_generators` charges `2 ^ (generators)`
(`Algebraic.LowerBound.Cutwidth.Wiring.Signals`). The hardness side of the
argument is saturated: at the charging vertex the realized pattern determines the
input up to `(K - 1)²` choices on each side, and no cut realizes more than `2 ^ n`
patterns, so every gain in the leading coefficient must come from the layout side.
Charging edges has a ceiling. Random cubic graphs have bisection width at least
`0.103295 h` ([Lichev and Mitsche](https://arxiv.org/abs/2009.00598), improving
Kostochka and Melnikov's `0.101 h`), and `MedianOrdering` gives cutwidth at most
pathwidth plus two on cubic graphs, so no universal cubic pathwidth coefficient is
below `0.1032`; the edge-charged assembly therefore cannot certify a circuit
coefficient above `1 + 1/0.2066 ≈ 5.84`, and realistic estimates of the random
cubic bisection constant put the practical limit lower. A coefficient of five or
more needs generator charging or a different compiler.

The same coefficient now holds for binary circuits augmented with arbitrary finite
commutative-monoid gates, provided their actual occurrence budget
`D = q + Σ ceil(log₂ |M_j|)` is `o(n)`
(`Aggregate.sourceReductionHardFamily_eventually_lt_size_gaussian`). Outgoing-transition
counting removes the need for invertible updates. The checked gate instances include
AND, OR, weighted modular gates, capped nonnegative weighted thresholds, and arbitrary
symmetric predicates. The conclusion counts total gates and retains the existing fixed
polynomial-time family; it does not improve the binary-only coefficient or cover an
unrestricted number of special gates.

Joint compression now replaces the occurrence budget by
`D = 2 ceil(log₂ |M|)` whenever every local contribution to the vector of special
registers factors through one finite commutative monoid `M`
(`Aggregate.Compressed.sourceReductionHardFamily_eventually_lt_size_gaussian`).
One state guesses all special outputs and another accumulates their simultaneous
check. The number of special gates and their dependencies are unrestricted; the
factorization and sublinear joint budget are the hypotheses. The submonoid generated
by all local contributions supplies a canonical instance. For a common prime
modulus `p`, the actual contribution matrix gives an automatic factorization with
exactly `p^rank` states and budget at most `2 rank ceil(log₂ p)`.
Thus sublinear rank suffices for fixed `p`, even with linearly many MOD gates.
This strengthens the scope of the sparse-aggregate theorem, not its coefficient.

A separate whole-basis theorem now removes that sparsity condition at a smaller
coefficient (`Aggregate.sourceReductionHardFamily_eventually_lt_realCapacity`).
Its exact capacity is `B = ordinaryCount + Σ log₂ |M_j|`, with no output guesses or
per-register rounding, and it proves `B > (1-ε)n` eventually. Register cardinalities
at most `r ≥ 2` give more than `(1/log₂ r-ε)n` gates; in particular B2 plus arbitrarily
many two-state AND/OR/parity aggregates retains a coefficient of one. The finite
bound is `n ≤ B + 2 ceil(log₂ K) + 7`. This uses classical one-way communication
accounting, credited to Roychowdhury–Orlitsky–Siu, rather than the cubic ordering bound.
The fixed family's two-sided rectangle and sumset-disperser properties are also
exposed in `Aggregate.Capacity.Polarity`.

Affine pairing and biased-message counting now improve the whole-basis coefficient
for signed unbounded AND/OR/XOR circuits, including every binary Boolean operation:
`Aggregate.Geometry.sourceReductionHardFamily_eventually_lt_size` proves
`(C-ε)n < size`, where `C=(1+2c)/(1+c)=1.15876032857...` and
`c=1-H₂(1/4)`. There is no depth, fanout, fan-in, or sparse-gate assumption. The
checked pairing lemma gives `2n ≤ g+h₂+2 ceil(log₂ K)`, where `h₂` counts conjunctions
with two distinct direct primary variables. Those same gates incur an entropy
deficit in the actual one-way protocol; exact subset averaging combines the counts.
Both the circuit geometry and the explicit-family asymptotics are checked.
Joint counting now strengthens this to
`Aggregate.Geometry.Joint.sourceReductionHardFamily_eventually_lt_size`, with
`C=(H₂(1/4)+3/4)/(H₂(1/4)+1/2)=1.19065368005...` and the same unrestricted basis
and fixed Boolean family. A graph of two-variable conjunction summaries receives
conditional costs according to whether a new edge has zero, one, or two already
used endpoints. Exact tables on at most four bits handle every sign pattern;
larger conjunctions and contradictions only decrease the required cost.

Shared primary controls improve the coefficient again to `1.22148505965...`
(`Geometry.Shared.sourceReductionHardFamily_eventually_lt_size`). A maximal pairing
of intersecting two-primary conjunctions pays extra affine restrictions by making
distinct gates constant. Retaining the stronger one-eighth bias for wide conjunctions
and averaging designated triples combines the two counts. The exact coefficient is
`(3-h+3r)/(2+2r)`, where `h=H₂(1/4)` and `r=1-H₂(1/8)`; strict improvement is proved.

Large majority fibers improve both coefficients again
(`Aggregate.Geometry.Fiber.sourceReductionHardFamily_eventually_lt_size` and
`Aggregate.Geometry.Inversion.fiberCoefficient_mul_sub_penalty_le_size`): the fixed
explicit family needs more than `(C_F - ε)n` signed unbounded AND/OR/XOR gates with
`C_F = (1 + c/2 + 7r/4 + ℓ)/(1 + r + ℓ) ≈ 1.2364849888`, where `c = 1-H₂(1/4)`,
`r = 1-H₂(1/8)`, and `ℓ = r/(2 log₂(3/2))`, and all coordinates of binary-field
inversion in any supplied linear basis need at least `C_I n - P_I` gates for `n ≥ 3`,
with `C_I ≈ 1.5644077959` and `P_I ≈ 0.5640721944`. Disjoint signed-pair majority
fibers are counted and combined with the residual-message bound, both entropy
bounds, and the affine geometry. The earlier `1.22148505965...` and
`1.54311234736...` theorems below remain checked but are no longer the best.

Conditioning the residual-message entropy on those same majority fibers now gives
`C ≈ 1.2453914029` for the fixed scalar family
(`Geometry.Fiber.Conditional.sourceReductionHardFamily_eventually_lt_size`) and
`I n - P` for binary-field inversion, with `I ≈ 1.5659486596` and
`P ≈ 0.6016050397`
(`Geometry.Inversion.conditionalFiberCoefficient_mul_sub_penalty_le_size`).
In the product of three-point pair fibers, any prescribed `d` distinct coordinates
have probability at most `(2/3)^d`. Thus surviving two- and three-literal summaries
save `1-H₂(4/9)` and `1-H₂(8/27)` bits. Entropy subadditivity needs no independence
between summaries. The same pairing and weighted receiver cut combine this with
both earlier entropy inequalities and affine geometry. The new inversion bound
has a stronger leading coefficient and a larger additive penalty; keep both
finite inequalities. All circuit assumptions and target families are unchanged.
An open next step is sharper joint entropy inside these conditioned fibers, with
every overlap charged against the same geometric pairing.

There is also a natural multioutput target: for every linear coordinate basis of
a field of size `2^n`, computing all bits of inversion (with `0⁻¹=0`) requires
`(3+2c)n-4c ≤ (2+c)g` gates in this basis when `n≥3`, with `c=1-H₂(1/4)`
(`Geometry.Inversion`). Thus the coefficient is `1.54311234736...`, strengthening
the retained `3n ≤ 2g+4` theorem. Independent output components modulo affine
primary functions require at least `n` conjunction generators. Balanced nonliteral
conjunction outputs have constant primary summaries, while multiple-primary
conjunctions have biased summaries. These information savings combine with the
four-point affine restriction obstruction. The field properties and circuit
deduction are proved. This slice does
not construct a canonical uniform family of fields and bases or prove a new
machine-runtime bound for its evaluator.
See the [geometry note](research/circuit-lower-bound-frontiers/larger-gates/geometry.md),
[pairing proof](research/circuit-lower-bound-frontiers/larger-gates/pairing.md), and
[follow-up audit](research/circuit-lower-bound-frontiers/larger-gates/followup-audit.md).
Historical priority is unresolved. The next targets are joint finite-state savings
for broader gate bases and an amortized U2 equality-case theorem. A MOD3 gate need
not become constant under one affine equation, and a three-successor U2 interface
can retain all its inputs; the audit records exact obstructions to those local shortcuts.

- [x] **Charge frontier vertices instead of crossing edges.** Done by edge-score
  decompositions (`Gaussian.exists_frontier_pathwidthBound`): scoring each edge by
  its normalized endpoint sum makes every threshold a pairwise event, so the
  Gaussian-star comparison reduces to the vector inequality
  `‖Σ y_e‖ ≥ ⟨Σ y_e, x_v⟩` and concavity of `arccos`, with no positive-threshold
  correction.
- [x] **Exact crossing probability.** Done (`gaussPi_between_le_arccos`): Sheppard's
  `arccos ρ / π` bounds the crossing probability at every threshold, giving
  `p = (3/(2π)) arccos((1 + 2√2)/4) ≈ 0.14035` and `L ≈ 4.5625`.
- [ ] **Nonlinear smoothing of edge keys.** Every factor-of-iid *linear* Gaussian edge
  key has adjacent-edge correlation at most `(1 + 2√2)/4` on the cubic tree (the top of the
  line-graph spectrum), so `0.14035` is optimal among linear keys. Monte Carlo on the tree
  suggests that nonlinear local smoothing beats it: replacing each edge key by the median of
  itself and its four neighbours gives about `0.1346`, and iterating a trimmed mean of the
  five keys gives `0.1344, 0.1319, 0.1305, 0.1294` after one to four rounds (that is,
  `L ≈ 4.86`). Ordering each gate of a fan-out-two core by the median of its three signal
  scores and counting crossing signals gives about `0.1312` per core vertex. These are
  numerical observations only; a proof needs bounds on nonlinear functionals of correlated
  Gaussians that hold in every cubic graph, which none of the current pairwise arguments
  provide.
- [ ] **Two-sided sweeps.** Sweep negative edges by their larger score and positive
  edges by their smaller score, joined through the sign-crossing graph. The
  combinatorial target is a terminal path-decomposition lemma for subcubic graphs:
  with `h₃` degree-three vertices and disjoint terminal sets `U, V` of degree at
  most two, first and last bags `U, V` and width
  `max(|U|, |V|) + h₃/2 + ⌈log₂(h + 1)⌉ + 3`. The target coefficient is
  `p = (3/(4π)) arccos(5/6)`, `L = 1 + 2π/(3 arccos(5/6)) ≈ 4.5760`, and needs the
  universal all-prefix theorem with arbitrary positive slack, not a bisection
  estimate.
- [ ] **Signal and generator layouts.** Prove an ordering theorem for the wiring
  network that bounds the generators of every charged edge set by
  `(A' + ξ)(s − n) + O(log)`; `Wiring.card_accepting_le_of_generators` then gives the
  coefficient `1 + 1/A'`, and the compression, median-ordering, and `FourN` assembly
  must be redone for the generator count. Linear Gaussian keys do not supply the
  gain. Giving all edges of one signal a single class score makes copy vertices free
  but charges a gate `(3/(2π)) arccos ((3κ² − 1)/2)` by `sum_arccos_star_le`, where
  `κ` is the inner product of its class scores with its own row: `κ = ρ` for a copy
  class scored by the copy row and `κ = √((1 + ρ)/2)` for a single edge, giving
  `0.1404`, `0.198`, `0.2425`, `0.2796` for a gate meeting `0, 1, 2, 3` copy classes
  (with the averaged bound), against the frontier's `0.1404 (1 + k/3)` for the gate
  plus its share of the copies. Only a gate meeting three copy classes gains, by
  `0.0012`, and every mixed gate loses. Mixed gates are unavoidable: `∑ fan-out = 2s`
  over `n + s − 1` signals forces at least `2n − 2` fan-out-one signals when fan-outs
  are at most two, hence at least `n − 2` singleton gate-to-gate classes in the core,
  so no uniform cubic constant below the frontier's follows from class scores. The
  generator saving needs nonlinear keys or a joint-event bound in the frontier
  ordering. Monte Carlo on random fan-in-two circuits at `s = 4.5 n`, laid out through
  the actual compression with median-of-edge-score orderings and finite kernels, puts
  signal counting about ten percent and generator counting about fifteen percent below
  edge counting in the same ordering; these are relative observations with no proof.
- [ ] **Rigidity and local repair.** Audit the four-star distance-kernel rigidity
  lemma first. A compactness argument would give some fixed improvement `δ > 0`
  over the two-sided coefficient, but no numerical `δ` is established.
- [ ] **Consolidate the Boolean pipeline onto `Complexity.Frontier`.** The Boolean
  wiring network, `FourN`, `Nondeterministic`, `Forget`, and `AverageCase` are special
  cases of the frontier method at `U = Bool`, `r = 2`. Derive their public theorems from
  the general ones, then retire the duplicated network and counting layers. The cubic
  `Compression` is the degree-three case of the mirrored degree-generic one, and the
  kernel, crossing, second-moment, and star lemmas of `Cutwidth.Gaussian` duplicate the
  mirrored ones, whose kernels are also degree-generic; the band-jump and vertex-score
  layouts still use the cubic copies. Keep `OrderingBound`, whose logarithmic error is
  sharper than `LayoutBound`'s, as the interface to them.
- [x] **Layout coefficients below one in degree `d ≥ 4`.** Done upstream and mirrored:
  Gaussian vertex layouts on multigraphs with parallel edges give `LayoutBound d A_d`
  with `A_d < 3/4` (`Frontier.layoutBound_degree`), `A_4 = 2/5`
  (`Frontier.layoutBound_two_fifths`), and `(7/4 - ε) n` at fan-in three. Open: whether a
  joint degree/correlation analysis, joint signal routing, or subcubic port-tree
  projection improves `A_d`.
- [ ] **Capacity supply theorems.** The frontier method's counting inequalities accept
  distinct signals, any determining transition code, pruned transition sets with a
  tail budget, and joint merge boundaries of a tree of regions. Each needs a universal
  layout or decomposition theorem with a smaller coefficient on compiled networks; the
  independent median update needs a quantitative gain uniform over cubic graphs and
  thresholds.

The arithmetic bridge is now checked in `MultiOutput.Polynomial`: arbitrary
fan-in-two polynomial gates computing any totally regular linear map over any
field require `(4.5625-ε)N` gates eventually. Formal differentiation at zero
gives a local linear realization on the original wires over infinite fields;
finite fields use the existing counting bound. A new field-independent rank-cut
lemma feeds the same layout proof, preserving the gate count without a separate
Menger theorem. Degree, coefficients, depth, and fanout are unrestricted.
`Polynomial.Cauchy` supplies the explicit rational-node matrix
`M(i,j)=1/(i-(N+j))` over every characteristic-zero field, including Q, R, and C.
`Polynomial.Arithmetic` proves the same lower bound for additions and
multiplications with arbitrary constant gates free: its constant-absorption
compiler emits exactly one polynomial gate per arithmetic operation.
Lev--Valiant supplies the classical `4N-o(N)` superconcentrator baseline;
no broader arithmetic record claim is made. The
[transfer audit](research/circuit-lower-bound-frontiers/transfer-ledger.md#transfers-to-other-circuit-models-audited-next-steps)
records why finite-alphabet, arbitrary higher fan-in, continuous, quantum, and
randomized variants need separate hypotheses or compiler arguments. Continuous
gates via invariance of domain and rational gates regular near a base point are
natural next bridges; neither extension is currently formalized.

## Uniform tensor families

`Algebraic.Tensor3.Dissociated` now defines one computable tensor family at every
ambient dimension `m`, independent of approximation parameters. Its complex
border rank is at least `(7/3-ε)m` eventually for every `ε>0`; in particular it
is eventually at least `17m/8`. Every integer coefficient uses at most `m+1`
binary digits. A bounded search chooses the periodic paired-cluster parameters
subject to both coefficient-size and finite-rank-error guards, and zero padding
handles even dimensions. This strengthens the motivating distinct-subset-sums
PDF's target with a different family, reusing the checked paired-cluster theorem.
The next steps are a machine-level polynomial-time evaluator and an explicit
convergence rate. Computability and polynomial output size alone are not an FP
certificate, and neither of those remaining statements is claimed proved.

## Descriptive complexity expansion

The expansion prompted by Senellart and Gnatenko's September 2026 paper is
specified in [`docs/DescriptiveComplexity.md`](docs/DescriptiveComplexity.md).
The completed layers provide second-order transport for universe-preserving
reductions, existential SO definability, tagged formula pullback and composition,
and reductions between invariant decision problems. Graph examples include the
existential SO definition of bipartiteness and a reduction by disjoint copies.
The pullback theorem follows Immerman's Proposition 3.5, including open formulas
and source-constant tuples; tagged composition is proved up to isomorphism.
Relation-variable renaming now has exact identity and composition laws,
open-formula satisfaction, size preservation, and preservation of FO matrices
and existential SO prefixes. Capture-avoiding conjunction and disjunction merge
the leading relation quantifiers without duplicating syntax: the result has
size `φ.size + ψ.size + 1`. Consequently `ExistSODefinable` is closed under
intersection and union with explicit prefix-form witnesses.
Boolean relation environments now represent exactly the semantic relation
environments. A computable evaluator checks FO matrices against supplied
Boolean tables, with correctness for arbitrary free element assignments and
exact agreement with the existing FO evaluator. Existential and universal
quantification over semantic relation environments can therefore use Boolean
tables. A concrete bipartition checker accepts exactly proper Boolean colorings.
Relation environments now have canonical binary truth-table encodings of exact
length `∑ n ^ arity`, with both round trips and rejection exactly on wrong
lengths. An existential-SO certificate checker consumes the prefix tables in
order, rejects missing or trailing bits, and evaluates the FO matrix. Soundness
and completeness hold for open formulas with supplied free environments. For
sentences, the encoded checker characterizes the full query language and has a
fixed polynomial certificate bound in input length. On bipartite graphs, the
certificate is one color bit per vertex and the checker agrees with the existing
Boolean-coloring evaluator.

The circuit track now compiles arbitrary FO formulas to the existing
`AC0Formula` representation. It proves satisfaction on relation tables and
one-hot constant blocks, exact polynomial tree size in the universe cardinality,
and depth at most the source formula's size plus one. A reusable realization
theorem converts these trees to actual unbounded circuits of exactly the same
size and depth at most one greater, at positive input width. A computable layout
now reads the exact positions in `encodeStruct`, and encoded length is strictly
increasing in universe size. The decoder has exact round trips, encoding
injectivity, and rejection precisely outside the encoder's image. The encoded
FO evaluator is proved correct for the full induced binary language.
Encoding validity now has a depth-three formula of size
`n + 4 + numConsts * (1 + n * (1 + n))`. Conjoining it with sentence expansion
gives circuits recognizing the exact query language, including malformed-input
rejection. These circuits form a family at all input lengths, with false output
at length zero and at lengths supporting no valid encodings. The proved
`FODefinable.queryFamily_mem_AC0` connects FO definability to the existing
nonuniform `AC0` class, with depth at most `φ.size + 5` and a polynomial size
bound in input length.

The machine track now has arithmetic addresses proved equal to the encoder's
enumerated positions. Tuple indices use little-endian base-`n` coordinates;
relation and constant addresses add the exact preceding block lengths. Bit
access, unary-cardinality parsing, these addresses, and structure/certificate
lengths have machine-level polynomial-time proofs. Explicit length, header, and
one-hot tests characterize the encoder's image. Bounded quantification over
polynomial-time bit tests proves `validEncodings_mem_P`, as well as a
polynomial-time predicate for successful decoding.

Fixed-formula evaluation now has a machine-level polynomial-time proof.
Constants use bounded search of their one-hot blocks, and first-order quantifiers
use the bounded-quantifier rules with polynomial-time free-variable values.
Combining evaluation with encoding validation proves
`FODefinable.queryLanguage_mem_P`; the existing `Sentence.evalEncoded` verdict
also belongs to `FP`. The formula is fixed in these results, and no logarithmic
space bound is claimed.

Existential-SO verification now also has a polynomial-time machine proof.
Arithmetic matrix evaluation reads the supplied relation tables, and prefix
checking consumes each block by polynomial-time slicing. Both agree with the
existing Boolean evaluators. `SOSentence.checkEncoded_mem_FP` gives the complete
verdict function, including malformed-input rejection, an `FP` implementation.
Together with the proved witness bound and guess-and-verify NTM, this proves
`ExistSODefinable.queryLanguage_mem_NP`, the upper direction of Fagin's theorem.

The universe-preserving reduction bridge is now proved. Numeric tuple decoding
reproduces the encoder's order, and fixed-formula truth-table generation belongs
to `FP`. `FOInterpretation.mapEncoding` computes the exact interpreted structure
encoding and maps every malformed input to `[]`. Its full output length is
bounded by the target encoding polynomial in input length.
`FOReduces.mapReducesPoly` lifts structural reductions to machine many-one
reductions. Together with the ESO upper bound, this gives an NP-completeness
criterion from an NP-hard source language and a structural FO reduction.

Tagged tuple encodings now have exact arithmetic semantics: tag and coordinate
packing, relation tables, and constant blocks produce the existing interpreted
structure's encoding, of full length `encodingLength W (tags * n ^ dim)`.
Its `FP` bound is the remaining part of the tagged encoding bridge.

Canonical numerical extensions now expose strict order, `BIT`, `ADD`, and `MUL`
as ordinary FO atoms, with proved semantics and computable expansions. Input
formulas embed without changing truth. Addition and multiplication are ternary
relations restricted from natural arithmetic, without modular wraparound.
Next add derived successor and endpoint formulas, then explicit formula
translations proving `FO[BIT] = FO[ADD, MUL]`. Keep this as a sequence of small
checked layers, with the corresponding blueprint nodes in each commit.

Other next priorities are the tagged encoding machine bound, tagged SO transport,
and the converse of Fagin's theorem. The NP-to-ESO direction still needs
a tuple-indexed computation tableau and a guessed order; Immerman--Vardi needs
fixed-point logic and both capture directions. The ordered `FO[BIT]` capture of uniform
`AC0` still needs a uniformity predicate and both capture directions. Domain restrictions
and exact projections remain distinct extensions.

## Quality gates

Every change must leave these green (CI runs all of them):

```bash
python3 scripts/lint_style.py
lake build --wfail
lake build --wfail Complexitylib.Classes.P.Cobham.Validation
lake build --wfail Complexitylib.Models.TuringMachine.SingleTape.Validation
lake build --wfail Complexitylib.Models.TuringMachine.Repetition.Validation
lake build --wfail Complexitylib.Circuits.Encoding.Validation
lake build --wfail Complexitylib.SAT.Tseitin.Machine.Validation
lake exe runLinter Complexitylib   # plus the five validation roots
lake env lean scripts/AxiomGuard.lean
lake env lean scripts/BlueprintCheck.lean
```

## Contributing

1. Find the node you want in the blueprint. Planned nodes whose dependencies
   are all formalized are ready to work on.
2. Check the levers before designing a machine.
3. Write the public statement first, in the surface module, and record the
   resource bound, representation, and malformed-input behavior in the module
   documentation.
4. Land definitions and structural lemmas first, then the finite or
   fixed-parameter theorem, then the asymptotic class-level statement.
5. Update the blueprint in the same change: add `\lean{...}` and `\leanok` to
   the node you formalized, or add the node if it is new.
6. Run the quality gates.

See [CONTRIBUTING.md](CONTRIBUTING.md) for style, naming, layering, and commit
conventions.

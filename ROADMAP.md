# Complexitylib roadmap

This roadmap is a contribution guide for extending Complexitylib from its current
machine- and circuit-level foundations into a broad, reusable formalization of
computational complexity theory. It is intentionally ambitious, but it is not a
list of promises. Each headline theorem is decomposed into intermediate artifacts
that are independently useful and small enough to review.

The ordering below is dependency-driven. A later track may be explored early, but
its final class-level theorem should normally wait for the shared encodings,
resource accounting, and finite-probability infrastructure on which it depends.

## Current baseline

The library already contains substantial foundations:

- A concrete Arora--Barak-style model of deterministic, nondeterministic, and
  probabilistic Turing machines over a fixed four-symbol alphabet, with explicit
  time and space predicates.
- Reusable machine combinators, Hoare-style specifications, unary registers,
  emitters, counters, pairing machines, multi-tape-to-single-tape simulation, and
  a universal-machine development.
- Definitions of major classes including `DTIME`, `NTIME`, `DSPACE`, `NSPACE`,
  `P`, `PPoly`, `PAdvice`, `NP`, `BPP`, `RP`, `ZPP`, `PP`, `PSPACE`, `EXP`,
  `NEXP`, `SC`,
  `FNP`, and `TFNP`, together with selected containments and closure results.
- A deterministic time-hierarchy theorem in a concrete, clock-constructible
  formulation.
- A bit-level SAT encoding, polynomial-time verifier, computation tableaux, and a
  full Cook--Levin reduction culminating in SAT NP-completeness.
- A typed Boolean-circuit model with size and depth, AND/OR bases, CNF and DNF,
  Shannon bounds, essential-input and gate-elimination lower bounds, Schnorr's XOR
  lower bound, nondeterministic quantification bounds, and a Valiant-style depth
  reduction theorem.
- A growing collection of concrete languages that exercise the machine API and
  witness nontrivial class membership.
- A logarithmic-cost random access machine model with a soundness theorem
  distinguishing it from the unsound unit-cost measure.
- A Fourier-analysis-of-Boolean-functions subtheory (`Complexitylib.BooleanAnalysis`,
  after Ryan O'Donnell): Chapter 1, with the parity functions as an orthonormal
  basis, Fourier coefficients/weights, and the mean/variance/convolution API — the
  analytic foundation for small-depth-circuit lower bounds and natural proofs.

This baseline is not yet a single unified theory. In particular, machine
encodings, circuit families, uniformity, advice, oracle access, interactive
protocols, and cryptographic security need common interfaces before their
headline equivalences can be stated cleanly.

## Guiding principles

1. **State the exact theorem variant.** Resource conventions, uniformity notions,
   error constants, zero-length inputs, promise behavior, and encoding choices
   belong in theorem statements or immediately adjacent documentation.
2. **Separate definitions, proof machinery, and surface theorems.** Definitions
   and public theorem statements should remain short enough to audit; large
   simulations and arithmetic proofs belong in `Internal` modules.
3. **Prefer reusable bridges over isolated headline proofs.** A verified circuit
   evaluator, transcript encoding, or finite counting lemma is more valuable than
   a one-off proof that bypasses the shared API.
4. **Account for resources compositionally.** Every construction should expose a
   concrete bound first and an asymptotic corollary second.
5. **Use finite counting before importing heavier probability machinery.** The
   current PTM semantics already counts functions `Fin T -> Bool`; exact finite
   arguments are often easier to compute with and audit.
6. **Preserve executable witnesses where practical.** Machines, circuits,
   reductions, encoders, and protocol verifiers should be definitions, not merely
   existential objects.
7. **Keep textbook abstractions honest about representations.** Complexity is
   measured on encodings. Parsing, malformed inputs, output length, and conversion
   between `List Bool` and `Fin n -> Bool` must be explicit.
8. **Land small steps.** A contribution should ideally add one definition, one
   structural lemma family, or one theorem layer and leave the repository building
   without errors or warnings.

## Dependency overview

```text
core API and encodings
  +-- deterministic/probabilistic finite counting
  +-- machine and circuit evaluators
  |     +-- nonuniform TM/circuit bridge + advice
  |     |     +-- BPP subset P/poly
  |     +-- uniform circuits <-> TMs
  |     |     +-- NC/AC uniformity
  |     |           +-- Barrington and bounded-depth lower bounds
  |     +-- canonical complete problems and reductions
  +-- protocol/transcript infrastructure
  |     +-- interactive-proof classes
  |           +-- sum-check and IP = PSPACE
  +-- oracle machines and security games
        +-- relativized worlds
        +-- pseudorandom functions
              +-- natural-proofs barrier
```

## Near-term tracks

### N0. Core API consolidation and proof ergonomics

**Goal.** Make foundational tape, run, encoding, and asymptotic facts available
from stable public modules so later work does not duplicate local lemmas.

**Prerequisites.** None beyond the existing library.

**Current progress.** The core model now exposes alphabet separation facts,
`Tape.ext`, initialized/started-tape cell and read lemmas, `Tape.move_cells`,
`Tape.write_head`, canonical `readBackWrite` no-op/move facts, canonical
register-cell facts, and DTM time-bound monotonicity. NTM traces now expose
left-end-marker preservation on every tape, canonical final-step splitting,
and indexed invariant induction without dependent prefix-cast plumbing, as
well as internal input/work/output head-growth bounds. Stable phase boundaries
now expose one public fixed-point certificate for the input, whole work family,
and output. Several large consumers have been migrated away from private copies;
endpoint/run lemmas and a few older local tape helpers remain. The first
serialized-evaluator boundary now composes the public validator, frame-preserving
rewind, and canonical pair splitter under one total `HoareTime` contract; doing so
exposed and repaired missing left-marker and frame facts instead of hiding them in
another controller-local proof.

**Staged milestones.**

- [ ] Add a canonical extensionality and simplification API for `Tape`, `Cfg`,
  `Tape.init`, `Γ.ofBool`, `TM.reachesIn`, and `NTM.trace`.
- [ ] Consolidate repeated endpoint-determinism, run-concatenation, halting, and
  time-bound monotonicity lemmas.
- [ ] Give all major constructions a named concrete time/space bound and a
  separate `BigO` theorem.
- [ ] Audit aggregation modules so public imports do not need to name proof-only
  implementation files.
- [ ] Add lightweight regression examples for core simplification behavior.
- [ ] Advance proof-level named-tape/effect contracts for executable TMs: name
  phase endpoints and tape frames once, then derive reusable composition rules
  before deciding whether syntax generation or a typed controller DSL is warranted.
  *Decomposed:*
  - [x] Add the opt-in `TM.Experimental.EmitSpec` contract and validate its
    heterogeneous sequencing rule on two complementary Tseitin pipelines. The
    concrete machines and theorem statements are unchanged; the consumer file
    shrank by 17 lines, but the 86-line shared module is not yet amortized.
  - [ ] Test the endpoint vocabulary in a separate construction where it removes
    material plumbing, then decide whether to add time-space/transducer dimensions
    or carry effects in authoring syntax.
- [x] Evaluate CREI's rose-tree machine (RTM) as a possible frontend and test its
  transferable first-order control-flow idea in a local vertical slice. *Decomposed:*
  - [x] Audit the upstream `rtm` branch and record the adoption decision. The
    pinned evaluation in `docs/N0-MachineAuthoring.md` rejects a direct dependency
    for now: the experimental stack is not root-tested or warning-clean and has no
    RTM-to-TM compiler or compatible all-reachable tape-space contract.
  - [x] Add an experimental first-order routine layer with structural lowering for
    calls, sequencing, and input iteration. The indexed `ForInputLoopSpec` and
    `ForInputLoopSpaceSpec` certificates recover exact execution and all-reachable
    space for `Experimental.binaryLengthRoutine = forInput (call binarySuccTM)`.
  - [x] Add a minimal structured imperative frontend for the logarithmic-cost RAM,
    compile sequencing, conditionals, and loops to absolute RAM jumps, and prove
    exact semantic/time/space preservation. The Hamming-weight vertical slice has
    an independent source proof, an exact transition formula, explicit
    logarithmic-time and peak-space budgets, quasilinear asymptotic corollaries,
    and a concrete compiled-RAM performance theorem. Generic internal resource
    certificates now handle finite register envelopes, real `finsum` space, and
    compositional sequencing, branching, and loops; the benchmark retains only
    its algorithm-specific invariant and arithmetic. That loop invariant bundles
    semantic facts with the register envelope, and straight-line command lists do
    not introduce a proof-only terminal `skip`. Its reserved-register input layout
    also exposes the raw RAM input ABI's lack of a uniform scratch region.
  - [x] Reimplement the existing finite-state `pairValidateTM` as a table-driven
    structured RAM program. The first direct implementation had exact `17 + 9n`
    transitions and explicit quasilinear logarithmic-time and peak-space bounds,
    but was a negative ergonomics result: its benchmark-specific files totaled
    882 lines versus 320 for the TM consumer, because transition-table address
    preservation remained bespoke while the TM version already used `scannerTM`.
  - [x] Extract a generic finite-state scanner compiler and certificate, then add
    a typed `FinEnum` interface so consumers never write numeric transition tables
    or state-refinement folds. The reusable layer proves exact source and
    compiled-RAM correctness, `9 + 3k + 9n` transitions for a `k`-state scanner,
    explicit logarithmic-time and peak-space bounds, and quasilinear asymptotics.
    PairValidate's benchmark-specific files shrink from 882 to 208 lines, below
    the 320-line TM consumer; its exact dense-table count is `24 + 9n` rather than
    the hand-specialized `17 + 9n`. Independent typed instances now cover the
    three-state LastBit scanner (`18 + 9n`) and the existing 27-state exact-3-CNF
    syntax automaton (`90 + 9n`) with direct language agreement. The 1,273-line
    shared layer is therefore validated across small, medium, and substantially
    larger finite controls, although sparse table initialization remains a useful
    constant-factor optimization rather than a correctness or asymptotic blocker.
  - [x] Add the first non-regular structured-RAM parser component for the serialized
    circuit evaluator: a terminated-unary cursor decoder with distinct success and
    exhaustion exits, exact transition counts (`10k + 16` through a terminator and
    `10n + 11` on truncation), explicit logarithmic-cost time/space, quasilinear
    asymptotics, and end-to-end compilation preserving the decoded value and suffix
    cursor. This isolates nested early-exit control before adding indirect memo
    reads and writes to the evaluator.
  - [x] Verify the decoded-gate mutable-data kernel for that evaluator. The
    branch-free 20-instruction program performs two indirect memo reads and one
    indirect append, preserves every existing wire, and carries exact transitions,
    logarithmic-cost time, peak space, and Boolean correctness through compilation.
    Grouping its straight-line code at six semantic boundaries avoids expansion of
    a twenty-update store term; the reusable `exec_basics_exists` lemma also lets
    semantic proofs establish exact execution before choosing resource envelopes.
    Before composition, the unary decoder and gate kernel totaled 1,976 lines
    versus 5,635 lines in the complete TM evaluator core. This was promising but
    not yet an end-to-end comparison because the RAM side still lacked a parser.
  - [x] Compose the cursor decoder and mutable-data kernel into one fixed
    serialized-gate step. The source and compiled correctness and resource chains
    are now checked:
    it retains the three fixed header bits, invokes the same unary loop twice,
    discovers the memo base at runtime, evaluates and appends the gate, preserves
    every old wire, and takes exactly `10(input₀ + input₁) + 67` transitions. The
    composition test exposed and fixed a real API defect: cursor offset and unary
    accumulator had been conflated because they coincide for only the first field.
    `CursorReady` now separates them and frames high data; `GateEval.ReadyAt`
    similarly supports an arbitrary memo base. The generic routine now also has an
    arbitrary-base envelope theorem: twenty steps cost at most eighty word widths
    and preserve the caller's bounded store while appending one memo cell. The
    complete serialized-gate slice transfers the explicit bounds
    `512(n + 1)(bitlen(n + 8) + 1)` for time and
    `(n + 8)(2 bitlen(n + 8))` for peak space to concrete RAM execution, where
    `n` is the gate-code-plus-memo length. It is now on the public RAM surface.
    Unary decode, generic gate evaluation, and their composition total 4,195 lines
    (419 definitions, 3,404 internals, and 372 surface), still below the 5,635-line
    complete TM evaluator core. This is encouraging rather than a final size win:
    the RAM slice handles one valid serialized gate but still lacks the outer gate-
    count loop, malformed-input controller, and final verdict. A layout audit found
    the precise prerequisite for an honest next comparison: this benchmark step
    infers its memo base from the end of the current gate, which is correct for
    `gate.encode ++ wires` but points at the *next gate* in a multi-gate stream.
  - [x] Run the bounded iterable-layout admission test before writing the outer
    controller. `GateStreamStep` now gives the routine separate code-cursor and
    memo-base inputs, uses two fixed continuation cells between control and memo,
    consumes a canonical gate followed by an arbitrary unread tail, appends its
    Boolean value, restores the exact next cursor and tail length, increments the
    memo count, and preserves both old wires and unread code. Structural lowering
    transfers the exact `10(input₀ + input₁) + 80` transitions and the source
    logarithmic cost/space measurements to the concrete RAM. The fixed region was
    materially better than the first dynamic-spill attempt, whose store-update
    proof exploded, and the experiment strengthened `GateEval` with a genuine
    caller-frame contract.

    The admission result is nevertheless negative for this register-level IR as
    a replacement for direct TM authoring. The checked iterable slice is 1,362
    lines. Retaining it beside the compact benchmark makes unary decode, gate
    evaluation, and both compositions 5,638 lines, already matching the 5,635-line
    complete TM evaluator core before an outer loop, malformed-input controller,
    final verdict, or closed iterable resource bounds. Replacing rather than
    retaining the compact composition leaves 4,373 lines, only a 22% reduction
    before those missing layers, far short of the factor-of-two marginal payoff
    required to justify more tangent work. Do not implement the outer evaluator in
    this IR. Keep the structured compiler and amortized scanner API available, but
    require a higher-level language with typed memory regions, procedures, and
    loop contracts before reopening the circuit-evaluator comparison.
  - [x] Test the next seemingly cheaper alternative before designing typed RAM
    regions: a sound-by-construction syntax over the already successful
    `BinaryRoutine` API. The prototype covered every verified binary primitive,
    sequencing, zero branching, and count-up loops; a roughly 200-line lowering
    and structural induction recovered the full pure-effect, emitted-stream,
    concrete-time, all-prefix-space, and transducer contract. It cut the
    initialization serializer's parallel structural soundness plumbing by about
    half, but failed the integration gate: compiling the established transparent
    routine definitions left opaque source-lowering terms in `effect`, `emitted`,
    `requires`, and `spaceBound`, disrupting downstream `simp`, `change`, and
    compositional space proofs. Retaining both source and routine expressions
    merely duplicated programs and erased the saving, so the prototype was
    removed. The positive result is the existing domain-specific `BinaryRoutine`
    boundary itself: it already powered the complete `FL` tableau serializer while
    retaining a concrete `TM` in every routine. Prefer such proof-carrying APIs to
    a universal frontend; reconsider syntax only when lowering has projection-
    level normalization and gives a net reduction on two consumers.
  - [x] Close the formerly scheduled rose-tree `Data`/`InPlace` lowering as
    deferred and optional, not implemented. It is not a dependency of the
    named-tape/effect work; revisit only when a real construction needs recursive
    Data-valued syntax and the bounded slice can meet all promotion gates.
- [x] Audit proof-engineering mechanics across representative machine and circuit
  constructions: inventory repeated state/tape/wire bookkeeping, run or trace
  stitching, semantic transport, and resource accounting, then prototype the
  smallest reusable lemma, combinator, tactic, or typed DSL layer that removes
  the duplication. Validate each proposed abstraction on at least two independent
  constructions before making it a shared interface. The completed audit is
  recorded in `docs/N0-MachineAuthoring.md`: `NTM.trace_snoc` and
  `NTM.trace_invariant` now serve repetition, SAT phase exits, `GuessBounded`,
  `PairSplit`, `PairBuild`, and SAT verifier/counter invariants; the tableau loop
  now reuses the generic paired-and-clamped width theorem instead of two local
  wrappers. `TM.phaseTransition_eq_self_of_reads_ne_start` now serves five stable
  `PairSelf` seams and both `ClockConstructible.mul_succ` seams, while the
  bounce-capable left-marker boundary remains explicit. The helper is
  cross-construction but not yet line-amortized; a combined stage DSL remains
  explicitly rejected.
- [ ] Standardize the low-level contracts that make those larger abstractions
  compositional: reusable tape-shape predicates, explicit preservation frames,
  appendable endpoints, and exact-time sequential/loop rules. Treat an attractive
  machine definition with a destructive or under-specified proof interface as an
  API defect, and repair the interface before building more controllers on it.

**Proof-engineering benchmark.** Evaluate proposed mechanics on three distinct
shapes: a straight-line child-machine pipeline, a loop/repetition controller, and
a serializer or circuit evaluator. Record which obligations remain bespoke
(routing cases, frame preservation, run stitching, semantic transport, and exact
cost arithmetic). A successful abstraction should keep the machine executable,
provide compositional correctness and resource theorems, remove a material amount
of repeated plumbing in at least two shapes, and avoid making ordinary local proofs
more opaque. Prefer small combinators and theorem APIs first; add syntax generation
or tactics only where the benchmark shows that lemmas alone do not address the
repetition.

**External design reference: CREI's RTM.** Keep the concrete `TM` as the
semantic target and complexity-theoretic ground truth. The active pipeline is
`concrete phase machines + proof-level effect contracts -> TM combinators -> TM`;
`Routine` supplies one experimental control-flow layer, and a rose-tree frontend
could eventually sit above it, but neither syntax is required to validate the
middle-layer contracts. CREI's experimental
[RTM](https://github.com/crei/cslib/tree/rtm/Cslib/Computability/Machines/RTM)
remains useful design evidence: rose-tree data gives natural typed encodings, its
program builder provides functional composition and loops, and `InPlace`
excludes escaping closures specifically so that multi-tape simulation is direct.
It is not a drop-in replacement for the middle layer: its semantics do not
express this library's one-sided named-tape frames, read-only input, append-only
output, exact `HoareTime`, or all-reachable auxiliary-space obligations, and a
verified lowering to the fixed four-symbol `TM` is not available.

The pinned compatibility audit, no-dependency decision, benchmark measurements,
and promotion gates live in `docs/N0-MachineAuthoring.md`. Revisit rose-tree
lowering only after the effect layer reduces plumbing in independent
constructions, a concrete roadmap task is blocked on recursive Data-valued
syntax, and a bounded slice can prove semantic refinement, finite-state
compilation, explicit time, all-reachable space, and complete frames. If those
triggers fire, `reverse (var 0)` remains the preferred diagnostic benchmark.

The serialized-circuit evaluator is the current end-to-end experiment: its
validator, pair splitter, tape scanner, memo-wire appends, and evaluator loop
should compose through public contracts without reopening transition-level proofs.
Track proof size and the kinds of residual obligations at each boundary so the
eventual controller DSL, if warranted, is driven by evidence from a real consumer.
The completed front-end slice records the first data point: the sequential machine
contracts compose directly, while conditional routing, normalization of the test
output, and exact branch-cost arithmetic still require bespoke plumbing. The slice
also showed that appendable-prefix contracts must expose the left marker explicitly;
that fact is now part of the reusable pair-split interface. Likewise, a staged
verdict is not compositional unless its output contract retains `Tape.StartInvariant`;
the front end now exposes that invariant for the core's final overwrite.
The evaluator controller adds a second mechanics experiment: a local
proof-carrying `TapeAction` makes the one-sided-tape safety condition structural,
eliminating the usual phase-by-phase `δ_right_of_start` proof. Keep it local until
another controller demonstrates that the same action vocabulary is genuinely
reusable. Its execution layer packages the `Fin 3` work-family boundary as one
named configuration with an eta theorem, eliminating repeated index routing from
exact full-frame proofs. The rewind and unary-count runs show that named
configurations, namespaced action constructors, explicit preservation frames,
and `reachesIn` composition handle straight-line phases cleanly. Use the positive
gate loop to measure the remaining routing, semantic-transport, and cost-accounting
duplication before extracting a shared combinator, tactic, or controller DSL. The
successful loop now supplies that measurement: phase-generic named-action lemmas
within the controller remove repeated configuration plumbing, but the two reference rewinds
and unary scans still need phase-specific proofs; transporting a pure gate result
also needs an existential runtime because `GateStepResult` deliberately omits the
first reference that controls the exact cost. The loop invariant itself remains
compact when it records the code suffix, memo frontier, counter remainder,
last-value/output correspondence, and one fixed maximum memo length. The
rejection branches confirm the same boundary: short headers and terminal
rejection steps compose through generic configuration lemmas, while the
first- and second-reference unterminated/out-of-range runners remain close
phase-specific twins. Keep those helpers local for now; one controller is still
insufficient evidence for a public DSL, but the duplication is a concrete target
for the cross-construction audit. Total branch assembly also exposed one useful
small seam: generalizing the empty-answer transition theorem over its untouched
code suffix eliminated a duplicate proof immediately, without introducing new
syntax or hiding the controller's execution order. Likewise, the repeated
head/invariant/cell obligations after verdict writes are now one local
`outputWriteBool_frame` contract, reused across successful and rejecting branch
assemblies.
The same slice exposed a quality-gate blind spot: environment linting followed
only the public root, not the required validation-only graphs. CI now lints all
three validation roots as well, so internal proof seams cannot silently accrue
missing docs, unused arguments, or unsafe simp declarations.

**Formalization hazards.** Broad `[simp]` attributes can make machine-step goals
explode or loop. Prefer projection lemmas and narrowly oriented rewrite rules over
marking full transition definitions as simp lemmas. Moving a theorem must preserve
its public name or provide a compatibility alias.

**Small entry tasks.**

- [x] Centralize tape extensionality, write-head/move-cell projections,
  initialized Boolean/blank tape facts, and canonical register-cell lemmas.
- [S] Add the remaining narrowly oriented projections for `write`, `move`, and
  `writeAndMove` as concrete consumers demonstrate the need.
- [S] Migrate the remaining older modules to the shared initialized-tape and
  Boolean-symbol lemmas, deleting their local wrappers where this stays clear.
- [x] Add `TM.reachesIn_snoc`, endpoint uniqueness (`TM.reachesIn_right_unique`),
  and `TM.step_eq_none_iff_halted`.
- [x] Promote the canonical pair codec and pair-splitting machine out of NP
  internals, with a genuine `initCfg` endpoint, stable tape frames, an exact
  encoded-length cost seam, and a frame-preserving `HoareTime` specification.
  This is the first serializer-shaped proof-engineering benchmark.
- [x] Recognize the image of the pair codec with the generic finite-state
  scanner, obtaining total malformed-input rejection in exactly `n + 2` steps
  plus a frame-rich lifted specification. This is a concrete benchmark win:
  the regular control logic needs only a fold invariant, while the scanner and
  lift APIs supply execution, resource, and unused-tape proofs.
- [x] Move canonical binary-string tape shapes into a neutral encoding module;
  make pair splitting expose its full appendable-prefix invariant; and give the
  right-scanner an exact linear-time, frame-preserving contract. This closes the
  proof-information seam between decoding a pair and appending memoized wires.
- [M] Inventory the repeated controller mechanics in the UTM, repetition, and
  Tseitin developments; extract one small generic child-call/routing layer before
  committing to a larger syntax or metaprogramming framework.
- [x] Extract fixed-power `BigO` closure from repeated circuit-size proofs and
  validate it in both deterministic unrolling and BPP amplification.
- [x] Add exact-semantics fixed-choice acceptance hardwiring as the single-run
  counterpart of the amplified fixed-seed wrapper.
- [S] Refresh module documentation that still describes completed proofs as
  skeletons.

### N1. Canonical bit-string, finite-function, and encoding bridges

**Goal.** Establish one shared representation layer between languages
(`List Bool`), fixed-length circuit inputs (`Fin n -> Bool`), natural-number
indices, and serialized objects.

**Prerequisites.** N0 is helpful but not required.

**Current progress.** Fixed-length Boolean strings now have a canonical
`List Bool` bridge. Fan-in-two AND/OR circuits also have a canonical proof-free
codec with exact decoding, explicit malformed-input rejection, a polynomial
bit-length bound, and a tagged family wrapper covering the empty input. The
remaining milestones below concern reusable codec abstractions and encodings for
other object types.

**Staged milestones.**

- [x] Define lossless conversions between lists of known length and
  `BitString n`, with round-trip, length, map, append, and indexing lemmas.
- [x] Give fan-in-two AND/OR circuits a canonical proof-free encoding with an
  exact partial decoder and a concrete polynomial bit-length bound.
- [x] Separate encoded circuit validity from evaluation, with explicit rejection
  of truncation, trailing data, bad tags, and non-topological references.
- [ ] Define a reusable `Encodable`-style interface specialized to binary strings:
  encoder, partial decoder, round-trip theorem, and size bound.
- [ ] Give canonical encodings to finite functions, machine states,
  configurations, and bounded transcripts.
- [ ] Add pairing and tagged-sum codecs compatible with the existing pairing
  language and polynomial-time machines.

**Formalization hazards.** Dependent equality between `Fin n -> Bool` values and
lists with proof-carrying lengths can dominate proofs. Keep conversions
computational, isolate casts behind named lemmas, and avoid making proof fields
part of extensional encodings. Size bounds must count bits rather than rely only on
injectivity.

**Small entry tasks.**

- [S] Add analogous `List.ofFn` bridge lemmas for a non-Boolean alphabet when a
  second consumer demonstrates the need for a generic API.
- [S] Add a codec for `Fin n` with an explicit `Nat.log2`-style length bound.
- [x] Encode/decode the four tape symbols and three directions, including malformed
  bit patterns (`Complexitylib.Models.TuringMachine.UTM.Encoding`: `Γ`, `Γw`, `Dir3`
  two-bit codecs with round-trip, length, injectivity, and `[true, true]` rejection
  lemmas).
- [M] Define a generic length-bounded codec combinator for lists.

### N2. Finite counting and error amplification toolkit

**Goal.** Build exact lemmas for random bit strings, bad-event counts, independent
blocks, majority, and union bounds. This is the common prerequisite for BPP,
interactive proofs, and cryptographic games.

**Prerequisites.** Existing `NTM.acceptCount`, `acceptProb`, and rational
probability definitions; N1 for encoded experiments.

**Current progress.** `Complexitylib.Classes.FiniteCounting` has the sample-space
cardinality `card (Fin T -> Bool) = 2^T`, the prefix/suffix block split packaged
as an `Equiv` (projection and concatenation maps inverse by construction), the
finite union bound `card_filter_exists_le`, and a strict-`majority` function with
its odd-length negation antisymmetry `majority_not_of_odd`. Boolean vectors now
biject with their true supports, giving exact `Nat.choose` counts for every
`popCount` fiber and exact binomial-tail counts for majority success/failure. The
`blocksEquiv` schedule extends this to the actual long machine seed space, with
weighted block-event fibers and an exact normalized odd-majority failure
probability. A concrete `12k + 1`-repetition theorem reduces error from `1/3` to
at most `1 / 2^k`. The executable fixed-time PTM repetition machine, its fresh
tape-bank layout, its exact random-bit schedule, and cancellation of ignored
administrative bits are now public. The wrapper's complete pathwise simulation,
exact acceptance-probability identity, and yes/no amplification bounds are proved
in `Complexitylib.Models.TuringMachine.Repetition.Correctness`, completing the N2
wrapper milestone.

**Staged milestones.**

- [x] Develop cardinality lemmas for `Fin T -> Bool`, restriction to prefixes,
  concatenation into blocks, and permutations of random bits (`card_finArrowBool`,
  `blockEquiv`/`blockFst`/`blockAppend`, `eventProb_map`).
- [x] Define finite event probability once and relate it to `Finset.card` and the
  existing rational PTM probabilities (`Complexitylib.Classes.EventProb`:
  `eventProb`, its basic laws, and `NTM.acceptProb_eq_eventProb`).
- [x] Prove union, complement, conditioning-by-partition, and product lemmas
  (`eventProb_union_le`, `eventProb_compl`, `eventProb_eq_sum_fiberwise`,
  `eventProb_block`, and the `popCount` complement count).
- [x] Formalize binomial coefficients and majority failure counts in the exact
  finite sample space used by machines (`blocksEquiv`,
  `card_blockEventCount_eq`, `card_blockMajority_eq_false`, and
  `eventProb_blockMajority_eq_false`).
- [x] Prove a concrete amplification theorem from error `1/3` to `2^-k` with a
  fully specified repetition count (`eventProb_blockMajority_false_le_two_pow`:
  `12k + 1` independent repetitions).
- [x] Lift the combinatorial theorem to a reusable PTM repetition construction.
  - [x] Define `NTM.repeatAtTime` with fresh work-tape banks, an exact
    `2 + k * (2 * T + 2)` schedule, explicit zero-time/zero-repetition behavior,
    and an executable regression guard.
  - [x] Prove the compact/full seed schedule alignment, exact constant-fiber
    count, and probability cancellation for administrative choice bits.
  - [x] Prove the pathwise trace simulation and derive the exact repeated-machine
    acceptance-probability/majority theorem
    (`NTM.repeatAtTime_trace_correct`,
    `NTM.repeatAtTime_acceptProb_eq_eventProb`).

**Formalization hazards.** Independence should not be smuggled in through an
informal product argument: the bijection between one long choice string and blocks
must be explicit. Rational inequalities involving powers and floors can be harder
than the counting argument. A crude but sufficient exponential bound is preferable
to formalizing an optimal Chernoff constant first.

**Small entry tasks.**

- [x] Prove `Fintype.card (Fin T -> Bool) = 2^T` in the form needed by
  `acceptProb`.
- [x] Define block projection and concatenation maps and prove they are inverse.
- [x] Prove the finite union bound for a list of predicates by card counting.
- [x] Implement a majority function on `Fin k -> Bool` and prove its complement
  symmetry.

### N3. Canonical complete problems and reduction infrastructure

**Goal.** Turn Cook--Levin into a reusable ecosystem of complete problems rather
than a single endpoint.

**Prerequisites.** Existing SAT semantics, encodings, verifier, and polynomial
many-one reduction.

**Current progress.** Polynomial many-one reductions form a preorder.
`TM.copyInputToOutputTM` proves `id ∈ FP` and `MapReducesPoly.refl`.
`TM.compositionTM` runs two function machines through a disjoint-tape,
output-to-input pipeline within `4·T_f(n) + 11 + T_g(T_f(n))`; polynomial normal
forms then give `mem_FP_comp` and unconditional `MapReducesPoly.trans`. The same
pipeline now runs a function computation before a language decider;
`mem_P_preimage` and `MapReducesPoly.mem_P` package closure of `P` under
polynomial-time preimages and reductions.

**Staged milestones.**

- [x] Prove transitivity, identity, composition-time, and class-closure lemmas for
  polynomial reductions in their most reusable forms. *Decomposed:*
  - [x] Generic `≤ₚ` reflexivity/transitivity lemmas parameterized by the
    required `FP` facts
    (`Classes/NP/Reduction.lean`: `MapReducesPoly.refl_of_id_mem`,
    `MapReducesPoly.trans_of_comp`).
  - [x] `id ∈ FP` — `TM.copyInputToOutputTM` copies the input tape to the
    output tape in `n + 2` steps (`TM.copyInputToOutputTM_computesInTime`),
    yielding `id_mem_FP` and unconditional `MapReducesPoly.refl`.
  - [x] `FP` closed under `∘` — a sequential-composition TM (run `f`'s machine,
    pipe its output tape to `g`'s input tape, run `g`'s machine) with a
    `poly ∘ poly = poly` time bound; then `≤ₚ` is transitive.
    - [x] Prove output length is bounded by running time and normalize `FP`
      witnesses to everywhere-valid monotone polynomial evaluations.
    - [x] Embed a machine into a disjoint middle block of work tapes with exact
      same-time simulation and arbitrary preserved frame tapes.
    - [x] Implement the output-to-input pipeline and compose the machines and
      time bounds (`TM.compositionTM_computesInTime`, `mem_FP_comp`, and
      `MapReducesPoly.trans`).
    - [x] Generalize the pipeline's final contract to decision verdicts, normalize
      `P` witnesses to polynomial evaluations, and prove closure under `FP`
      preimages and polynomial reductions (`TM.compositionTM_decidesInTime`,
      `mem_P_preimage`, and `MapReducesPoly.mem_P`).
- [~] Define and relate SAT, CNF-SAT, and 3SAT encodings; prove a size-controlled
  Tseitin transformation. *Decomposed:*
  - [x] Name the existing encoded CNF problem as `CNFSAT.language`, expose
    injective encode/decode characterizations, and define the exact-3 restricted
    decoder and `ThreeSAT.language`.
  - [x] Give a total fresh-variable CNF-to-3CNF transformation, including an
    empty-clause contradiction gadget and wide-clause chains; prove exact-3
    shape and equisatisfiability (`CNF.to3_is3CNF`,
    `CNF.to3_satisfiable_iff`).
  - [x] Prove structural freshness bounds and the honest unary-codec bound
    `|encode (to3 φ)| ≤ 96 · (|encode φ| + 1)²`; lift the typed construction to
    a total semantic bit-string reduction (`ThreeSAT.reduction_correct`).
  - [x] Prove `ThreeSAT.language ∈ NP` directly by intersecting the existing SAT
    witness verifier with a finite-state exact-3 syntax checker.
  - [x] Implement the validation-first streaming transducer and its concrete
    register-machine controller, with a pure typed-token specification,
    executable regression guards, an exact controller simulation, and an
    explicit quartic time bound.
  - [x] Implement `ThreeSAT.reduction` in `FP`, derive
    `CNFSAT.language ≤ₚ ThreeSAT.language`, and transfer NP-completeness
    (`ThreeSAT.reduction_mem_FP`, `cnfsat_le_language`, `NPComplete_language`).
  - [ ] Add a codec/language for general `BoolFormula` SAT and relate it to the
    established CNF-SAT surface without introducing a third formula syntax.
- [ ] Add standard NP-complete graph languages such as CLIQUE, VERTEX-COVER, and
  INDEPENDENT-SET with explicit codecs.
- [~] Add TQBF/QBF syntax and semantics as the canonical PSPACE problem.
  *(`Complexitylib.SAT.QBF`: `QBF` syntax, `QBF.eval` semantics, quantifier
  substitution lemmas, `freeVars` + semantic locality `eval_eq_of_agree`, and the
  closed-formula TQBF layer `Closed`/`IsTrue`/`eval_closed_eq` all done; only the
  PSPACE-completeness theorem itself remains.)*
- [ ] Prove one PSPACE-completeness route only after the space-simulation API is
  stable.

**Formalization hazards.** Textbook reductions often silently assume random-access
arrays, fresh-variable generation, or unary/binary number encodings. The reduction
machine must produce the exact language encoding, and output length bounds must be
proved before polynomial-time membership.

**Small entry tasks.**

- [S] Add reduction identity and transitivity lemmas with concrete composed time
  bounds.
- [x] Define 3CNF syntax as either a refinement or a predicate on the existing CNF
  (`Complexitylib.SAT.ThreeCNF`: `CNF.Is3CNF` predicate, decidable, with cons
  characterization and renaming-preservation).
- [x] Implement clause padding and prove equisatisfiability
  (`Complexitylib.SAT.ThreeCNF`: `Clause.padTo3`/`CNF.padTo3`, `padTo3_eval`,
  `padTo3_satisfiable_iff`, `is3CNF_padTo3` for width `1…3`; wide-clause Tseitin
  splitting still open).
- [x] Add graph adjacency-matrix encoding with decode/encode and size lemmas
  (`Complexitylib.Classes.FiniteCounting`: `card_adjMatrix` — `2^(n·n)` directed
  graphs on `n` vertices — and `adjMatrixEquivBitVec`, the row-major
  adjacency-matrix ↔ `n²`-bit-string bijection, encode/decode inverse by
  construction; compose with the existing `BitString`→`List Bool` bridge for the
  serialized form).

## Mid-term tracks

### M1. Circuit families, uniformity, and the TM--circuit bridge

**Goal.** Connect the existing finite circuit model to language classes and prove
machine/circuit characterizations with explicit uniformity.

**Headline theorem: `P = logspace-uniform SIZE(poly)` (Arora–Barak Theorem 6.7).**
A language is in `P` iff it is decided by a logspace-uniform polynomial-size circuit
family. This is the central M1 payoff and factors into the two simulation directions.
Uniformity is **logspace** (an `FL` generator, Arora–Barak Definition 6.5), not the
weaker P-uniformity, so the same notion scales down to `NC`/`AC` later.

- **Circuits → TMs (`UniformPPoly ⊆ P`).** A polynomial-time DTM, given `1^n`, runs
  the log-space generator (`FL ⊆ FP`) to produce the length-`n` circuit code, then
  evaluates that code on the input with a memoized topological evaluator — all in
  polynomial time. *Decomposed:*
  - [x] Poly-time DTM circuit-code evaluator: validate and memoized-evaluate a
    tagged family code paired with its input, with a polynomial running-time bound
    (the fan-in-two encoding, exact decoder, topological validator, and array-backed
    iterative evaluator already exist as pure functions — this is their DTM
    realization and timing).
    - [x] Validate the outer pair on every input, rewind without destroying tape
      frames, and stage canonical code/input prefixes on distinct work tapes in
      time `4n + 16`; malformed inputs cannot enter the evaluator core.
    - [x] Define the total three-tape streaming controller: it parses the tagged
      code once, consumes the declared unary gate count, performs unary memo-wire
      lookups, appends one value per gate, and rejects malformed inner codes.
      Executable guards cover both tags, shared gates, invalid references,
      trailing garbage, and empty circuits.
    - [x] Prove the pure counted gate stream agrees with `evalCode`, including
      malformed codes, and lift it to the tagged `evalFamilyCode` semantics.
      Extract exact binary-cursor, marker-boundary, and named-action proof seams;
      promote the duplicated canonical-cell lemma to the neutral tape API.
    - [x] Prove the machine controller realizes the pure stream and give its
      quadratic `HoareTime` bound. The neutral `Tape.HasBinarySuffix` cursor API
      has also been extracted and adopted by the SAT verifier for this proof.
      - [x] Package the three named work tapes behind one exact configuration
        seam; prove both initial rewinds with full frames in exactly
        `|code| + |input| + 4` steps; route every family-tag case; and complete
        the well-formed empty-family branch from staging frontier to halted
        verdict in exactly nine steps.
      - [x] Scan a terminated unary gate count in exactly `g + 1` steps, preserve
        its left marker, and rewind it in exactly `g + 2` more steps to the
        gate-loop counter shape.
      - [x] Prove every successful controller-ordered gate attempt with exact
        cost `p + 2r₀ + |memo| + 11`, bridge it to `gateStep? = some`, and give
        the uniform bound `4|memo| + 9`.
      - [x] Induct successful `gateStream?` runs through the exhausted-counter
        check and compose the positive-family run from the staging frontiers
        under `positiveCoreRunBudget`; prove the concrete bound
        `20(|code| + |input| + 1)^2` whenever the unary gate count fits in the
        serialized code.
      - [x] Prove every failed `gateStep?` attempt, including truncated headers,
        unterminated unary references, and out-of-range memo reads, within
        `4|memo| + 8`; induct every rejecting counted gate stream under the same
        `gateLoopBudget`, including exhausted no-gate and trailing-data cases.
      - [x] Complete malformed unary-count and empty-family rejection, lift the
        tagged controller to total defaulted `familyStream?` agreement
        (`none ↦ false`), and expose `evalFamilyCoreTM_hoareTime` under
        `evalFamilyCoreTime = 20(|code| + |input| + 1)^2`.
    - [x] Overwrite the staging verdict with the evaluator result on every valid
      outer pair, prove agreement with `evalFamilyPair?`, and package a polynomial
      running-time bound.
  - [x] Compose the log-space generator with the evaluator; prove the resulting DTM
    decides the family's language in polynomial time. *Decomposed:*
    - [x] Prove the generic function-to-decider composition theorem, normalize `P`
      and `FP` time witnesses to polynomial evaluations, and derive closure of `P`
      under `FP` preimages (`TM.compositionTM_decidesInTime`,
      `mem_P_iff_decidesInTime_polynomial`, and `mem_P_preimage`).
    - [x] Prove the bounded reduced-configuration theorem for total log-space
      transducers and conclude `FL ⊆ FP` (and the parallel containment `L ⊆ P`).
    - [x] Implement in `FP` the family-specific preprocessing map
      `x ↦ pair (gen (unaryList |x|)) x`, preserving the original input while the
      generator runs on unary length (`unaryLength_mem_FP`,
      `mem_FP_pairWithInput`, and `generatorEvalInput_mem_FP`).
    - [x] Apply evaluator correctness through `mem_P_preimage` and conclude
      `UniformPPoly_subset_P` (`circuitEvalLanguage_mem_P` packages the verified
      evaluator language).
- **TMs → uniform circuits (`P ⊆ UniformPPoly`).** Unroll a `T(n)`-time DTM into a
  computation-tableau circuit of size `poly(T(n))` computing its output bit, and show
  the code map `1^n ↦ C_n` is computable in **log space** (logspace-uniform).
  *Decomposed:*
  - [x] Compile one deterministic transition step (configuration → next
    configuration, over the fixed-width tape window a step touches) into a Boolean
    circuit block; prove it computes `step` (the generic NTM compiler specializes
    to `tm.toNTM`).
  - [x] Tile the step block over a bounded tableau into a full circuit; prove
    semantic correctness (output bit = acceptance) and a `poly(T(n))` size bound
    (`TM.unrollingCircuitFamily`, with `P_subset_PPoly` as the nonuniform class
    theorem).
  - [x] Prove the tableau-circuit emitter is computable in log space (in `FL`) — the
    regular tableau structure makes the connection function log-space computable —
    giving logspace-uniformity, and conclude `P ⊆ UniformPPoly`. (The emitter being
    in `FL` rather than merely `FP` is the extra cost of matching Arora–Barak, and is
    what makes the notion reusable for `NC`/`AC`.) *Decomposed:*
    - [x] Expose a deterministic unrolling family reconstructed directly from its raw
      tableau gate list. `TM.directUnrollingCircuitFamily_encodeAt` identifies the
      complete tagged family code with `TM.directUnrollingCode`, avoiding the repeated
      typed hardwiring transformation while retaining exact semantics and cubic size.
    - [x] Flatten the positive direct-unrolling raw circuit into an initialization
      fragment, a canonical layer-ordered stream of base-independent fixed-size step
      fragments, and one final acceptance gate. The closed forms for every layer's
      configuration base, first unused wire, and gate count give the append-only
      serializer an exact numeric schedule without replaying proof-level trace state.
    - [x] Regularize the positive family to a closed cubic gate count by appending
      semantically dead constant gates and one final copy of the original acceptance
      wire. The padded raw list is well formed, has exact size `B(n) + 1`, computes
      the same bounded trace bit, and eliminates a preliminary gate-counting pass
      from the log-space generator.
    - [x] Expose the exact stack-free raw compilation order for the variable-length
      right folds used by transition formulas: children stream forward, one identity
      constant follows, and connector gates stream in reverse child order with
      explicit wire references. This removes the need to store a linear formula stack.
    - [x] Add compositional all-reachable space contracts. `TM.HoareSpace` and
      `TM.HoareTimeSpace` now compose through `seqTM`, preserve the transducer
      discipline, and package fresh-start contracts as `TM.ComputesInSpace` without
      mistaking a terminal head bound for a whole-run space proof.
    - [x] Add the binary-counter and fixed-polynomial arithmetic substrate needed to
      enumerate polynomially many gates and unary-coded wire references in logarithmic
      auxiliary space. *Decomposed:*
      - [x] Add canonical fixed-width little-endian natural-number encodings with exact
        length, modular and fitting-value round trips, fixed-width injectivity, and a
        bridge to the standard rewound binary-tape shape.
      - [x] Add an append-on-overflow little-endian successor subroutine with an exact
        frame-preserving endpoint, concrete time bound, all-reachable space contract,
        and one-way-output proof.
      - [x] Convert input length to a logarithmic-width binary counter without
        materializing unary work fuel. `TM.binaryLengthTM_reachesIn_frame` gives
        the exact runtime and endpoint frame,
        `TM.binaryLengthTM_hoareTimeSpace` covers every reachable configuration,
        and `TM.binaryLengthSpace_bigO_log` proves the explicit budget logarithmic.
      - [x] Add the canonical binary count-up loop substrate for streaming
        emitters: distinct counter and limit tapes, exact full-width
        comparison/rewind timing, exact iteration certificates, all-prefix
        auxiliary-space accounting, and structural one-way-output closure. This
        lands the reusable loop layer, not the direct-unrolling serializer.
      - [x] Build canonical binary addition from that loop: a preserved source,
        updated destination, and distinct zeroed scratch counter now have an exact
        literal-frame endpoint, width-based all-prefix space bound, and reusable
        one-way-output contract. This permits repeated-addition multiplication
        without using unary work counters.
      - [x] Build canonical binary multiply-add as a nested count-up loop over
        binary addition. It preserves both operands, updates only the accumulator,
        restores both private counters literally, and proves an all-prefix bound
        controlled by operand and final-accumulator widths.
      - [x] Add canonical positive binary predecessor with exact ripple-borrow
        semantics, including high-bit erasure at powers of two, a literal frame,
        and a width-based all-prefix bound. This supplies reverse connector
        countdowns without storing formula spines.
      - [x] Validate that loop at the circuit-code boundary: from a preserved
        canonical binary value and a distinct zero scratch counter,
        `CircuitCode.Machine.emitNatCodeTM` appends its terminated-unary
        `NatCode`, restores the complete input/work frame (including zeroed,
        reusable scratch), satisfies one-way output, runs within
        `emitNatCodeTime value`, and has the all-prefix auxiliary-space bound
        `initialSpace + 2 * value.size + 5`. Loading or changing the preserved
        value remains the caller's responsibility.
      - [x] Compose the circuit-code leaf used by the eventual tableau stream:
        `CircuitCode.Machine.emitRawGateTM` emits the fixed operation/negation
        header and two dynamic terminated-unary wire references from preserved
        binary tapes, restores its reusable zero scratch and complete frame,
        and carries explicit time, all-prefix space, and transducer contracts.
      - [x] Add fixed-polynomial evaluation and the remaining binary arithmetic and
        indexing operations needed by the raw tableau serializer. Fixed-polynomial
        Horner evaluation now has exact framed semantics and an honest logarithmic
        all-prefix space bound; the initialization block is also exposed as an exact
        natural-index schedule with no run-time formula or configuration syntax.
    - [x] Implement the append-only raw-tableau serializer and prove that the sound
      routine's pure output is exactly the padded direct-unrolling code at every length.
    - [x] Package the canonical-entry domain through compact semantic preconditions
      and obtain a total fresh-input `ComputesInSpace` theorem for the exact
      once-normalized padded-code function.
    - [x] Prove the serializer's explicit all-prefix space bound is logarithmic,
      conclude that its code function is in `FL`, package `P_subset_UniformPPoly`,
      and combine both directions. *Decomposed:*
      - [x] Give every serializer primitive and the complete transition-step
        routine a compositional width certificate. The step theorem follows the
        exact formula and delayed-copy trajectories through every nested loop and
        bounds the advertised auxiliary space at every routine prefix.
      - [x] Construct one explicit polynomial envelope for every reachable
        transition-loop entry, lift the local certificate through the whole
        tableau program, and derive the logarithmic `ComputesInSpace` theorem.
      - [x] Package the exact padded-code function in `FL`, prove
        `P_subset_UniformPPoly`, and combine both containments.

**Definitions for the headline.** [x] The `UniformPPoly` class is defined
(`Complexitylib.Classes.PPoly.Uniform`): `CircuitFamily.Uniform F` asks the tagged
code map `1ⁿ ↦ F.encodeAt n` (via the existing family codec) to lie in `FL`
(logspace-uniform, Arora–Barak Definition 6.5), and `UniformPPoly` is the languages
decided by a logspace-uniform polynomial-size family. The trivial containment
`UniformPPoly_subset_PPoly` is proved (forget the generator); the headline is
`UniformPPoly = P` (Arora–Barak Theorem 6.7). The Cook–Levin tableau infrastructure
already in the library (`SAT` reduction emitters) is related but is a CNF
*satisfiability* encoding, not a deterministic output-computing circuit. The
dedicated functional unrolling and its log-space emitter are now complete:
`TM.paddedDirectUnrollingCode_mem_FL`, `P_subset_UniformPPoly`, and
`UniformPPoly_eq_P` package the exact normalized code map and both containments.

**Prerequisites.** The N1 list/`BitString` bridge, the existing typed
`Circuit.eval` semantics, and stable machine composition/time accounting from
N0. The proof-free circuit codec and polynomial-time DTM evaluator are M1
deliverables, not prerequisites.

**Current progress.** `BitString` now has a canonical `List.ofFn` serialization
with round trips. `CircuitFamily` handles positive lengths with ordinary typed
circuits and records the empty-input answer explicitly. The library also has
total family size/depth functions, pointwise bounds, a concrete polynomial-size
predicate, `SIZE`, and the nonuniform class `PPoly`, together with its big-O
power characterization. Fan-in-two circuits now have a canonical proof-free
terminated-unary encoding, exact decoder, topological validator, array-backed
iterative evaluator, semantic equivalence with `Circuit.eval`, and a concrete
polynomial bit-length bound. Functional machine unrolling now has a bounded
one-hot configuration layout, initialization and one-step compilers, and a
complete tiled trace fragment with exact semantics, topology, and a cubic size
bound. A final halt-and-output gate now turns that trace into a typed
single-output circuit, with canonical choices-first evaluation and accepting
choice count exactly equal to `NTM.acceptCount`. Fixed-choice hardwiring now
specializes this construction to a canonical deterministic circuit family.
`TM.DecidesInTime.unrollingCircuitFamily_decides` proves exact semantics,
`TM.unrollingCircuitFamily_size_bigO` gives size `O(n^(3d))` for time `O(n^d)`,
and `P_subset_PPoly` packages the direct nonuniform containment.
The reverse uniformity path now has a syntax-stable target as well:
`TM.directUnrollingCircuitFamily` reuses primary wire zero for the choice inputs
ignored by `tm.toNTM`, reconstructs the positive member directly from
`acceptanceRawCircuit`, and proves that its tagged serialization is exactly
`TM.directUnrollingCode`. This removes typed prefix hardwiring from the
log-space emitter without changing deterministic trace semantics or the cubic
size estimate. Its positive raw circuit is now also flattened into initialization,
canonical fixed-size transition fragments with closed-form wire bases, and the
final acceptance gate. The canonical append-only binary routine realizes that
stream exactly, including the zero-length tag, and its all-prefix polynomial
width certificate packages the resulting code function in `FL`.
Polynomial advice now has an explicit self-delimiting input convention,
pointwise polynomial-length predicate, advised decision semantics, and a
hardwired family construction. `PAdvice_subset_PPoly` proves the
advice-to-circuit direction, while `PPoly_subset_PAdvice` uses canonical member
encodings with the serialized evaluator for the reverse direction;
`PAdvice_eq_PPoly` packages the equivalence. The evaluator front end has a total
linear-time validate/rewind/split contract for its outer pair encoding. Malformed
machine inputs retain fresh work tapes and cannot reach the evaluator core;
valid inputs expose appendable code and data prefixes on named work tapes. A
three-tape fused evaluator controller now executes both family tags and memoizes
topologically ordered gates. Its pure counted-gate stream now agrees with the
existing exact codec and evaluator. Exact full-frame machine proofs now cover
the initial rewinds, exhaustive tag routing, the well-formed empty-family run,
terminated unary-count setup, every successful gate attempt, and the complete
successful positive gate loop from staging frontiers under a named quadratic
budget. Bounded machine runs now also cover every pure one-gate failure and the
complete rejecting counted gate loop, including exhausted no-gate and trailing
data. Exact malformed unary-count and empty-family runs now close the remaining
tagged branches. `familyCore_fromFrontiers_run` proves total defaulted agreement
with `evalFamilyCode`, and the public `evalFamilyCoreTM_hoareTime` packages the
concrete quadratic core bound. The total `evalFamilyTM` now composes that core
through outer validation and staging: `evalFamilyTM_hoareTime` agrees with
`evalFamilyPair?` on every raw input, `evalFamilyTM_decidesInTime` decides
`circuitEvalLanguage`, and `evalFamilyTime_bigO_quadratic` proves the complete
budget is `O(n²)`. Canonical family codes have length `O(n^(2(d+1)))` when
family size is `O(n^d)`; evaluating them as advice takes `O(n^(4(d+1)))`.
The uniformity dependency path now has an exact finite reduced-configuration
theorem for one-way-output transducers: bounded input/work observations plus
the observable output frontier determine future execution, so a halted run has
one distinct snapshot per time index. The resulting explicit time bound is
polynomial under logarithmic auxiliary space, yielding both `L_subset_P` and
`FL_subset_FP`.
The forward uniform circuit bridge is now complete: a reusable unary-length
transducer and computed-value/input fanout combinator build
`pair (gen (unaryList |x|)) x` in `FP`; preimage closure then applies the verified
quadratic serialized evaluator and yields `UniformPPoly_subset_P`.
The reverse emitter's binary substrate is complete: canonical count-up loops,
addition, multiply-add, predecessor, copying, fixed-polynomial evaluation,
terminated-unary natural codes, and raw-gate emission all have exact effects,
reusable scratch frames, all-prefix space certificates, and transducer closure.
The concrete direct-unrolling controller composes those pieces through
initialization, every packed transition layer, finalization, and the zero/positive
branch. A single explicit polynomial bounds every reachable work value; binary
width then gives the logarithmic-space theorem. The deferred rose-tree lowering
was not needed on this dependency path.
Independently, `BPP_subset_PAdvice` follows from the existing
`BPP_subset_PPoly` theorem.

**Settled conventions.**

- A circuit family has one Boolean output, a typed circuit `C_n` at each positive
  length, and an explicit bit at length zero.
- Size and depth have total pointwise bound predicates; polynomial size has both
  a concrete natural-polynomial definition and a `BigO` power characterization.
- `PPoly` is the nonuniform polynomial-size circuit class over `Basis.andOr2`.
  Its asymptotic meaning matches the literature, while exact `SIZE(s)` uses the
  library convention that excludes input vertices and makes negation flags free.

**Uniformity convention.** `UniformPPoly` uses an `FL` generator on unary `1^n`
to produce a tagged family encoding: the tag distinguishes the length-zero output
bit from a positive-arity circuit code. P-uniformity may be introduced separately
if a later theorem specifically needs the weaker notion.

- Later, direct-connection or DLOGTIME uniformity for `NC`/`AC`. It should not be
  conflated with P-uniformity.

The existing `Circuit` type assumes nonzero input and output arities. The family
API resolves this deliberately: positive lengths use typed circuits, while the
unique empty input has an explicit `emptyOutput` bit. That convention must be
preserved by serialized encodings and uniform generators.

**Staged milestones.**

- [x] Define circuit-family semantics for `Language`, including conversion between
  lists of length `n` and `BitString n`.
- [x] Encode positive-arity circuits, reject malformed or non-topological codes,
  evaluate them iteratively, and prove agreement with typed circuit semantics
  plus a concrete encoding-length bound.
- [x] Add the tagged family wrapper and prove functional correctness at every
  length, including the explicit empty-input answer.
- [x] Build a DTM that validates and evaluates a tagged family code paired with
  its input in polynomial time, including the explicit length-zero case.
- [x] Prove the circuits-to-machines direction for the chosen logspace-uniform
  convention: `UniformPPoly_subset_P` promotes the `FL` generator to `FP`,
  constructs the evaluator input, and applies the verified evaluator through
  `mem_P_preimage`.
- [x] Build a functional computation-tableau/unrolling construction from a
  time-bounded DTM to a bounded-fan-in circuit computing its output bit.
- [x] Prove semantic correctness and a concrete polynomial size bound for the
  nonuniform unrolling construction (`TM.unrollingCircuitFamily` and
  `P_subset_PPoly`).
- [x] Define advice TMs and prove equivalence between polynomial advice and
  nonuniform polynomial-size circuits. `Advice`, `PolynomialAdvice`, `PAdvice`,
  `PAdvice_subset_PPoly`, `PPoly_subset_PAdvice`, and `PAdvice_eq_PPoly` complete
  both directions. The reverse direction reuses the serialized circuit-evaluator
  DTM rather than introducing a second evaluator.
- [x] Implement the tableau-circuit code emitter in `FL`, prove
  `P_subset_UniformPPoly`, and combine it with `UniformPPoly_subset_P` for the
  logspace-uniform equality.
- [x] Introduce `SIZE` and `PPoly` (`P/poly`) using the stable family conventions.
- [x] Introduce `DEPTH`, `NC^i`, and `AC^i` after uniformity and zero-length
  conventions have been propagated through the existing `AC0` definition.
  (`Circuits/DepthClasses` uses total `CircuitFamily` semantics, polynomial
  size, and the explicit envelope `c·(log₂ n + 1)^i`; `NC0`, `NC1`, and the
  repaired `AC0` are specializations, and both hierarchies are monotone in
  `i`. These names are explicitly nonuniform.)

**Formalization hazards.**

- A Cook--Levin CNF expressing an accepting computation is not a circuit that
  computes the unique output of a deterministic run; use the dedicated functional
  unrolling construction rather than transporting SAT satisfiability semantics.
- The circuit generator's input length is `log n` if `n` is binary. Standard
  P-uniformity usually measures generator time polynomial in `n`, so encode `1^n`
  or state the convention explicitly.
- Circuit evaluation time depends on encoding validity, gate order, and fan-in.
- The evaluator consumes one machine input, so use the existing `pair code x`
  representation and account for its exact length rather than treating code and
  data as two implicit inputs.
- The current recursive typed evaluator can recompute shared subcircuits
  exponentially. Runtime theorems must use a validated topological encoding and
  a memoized/streaming evaluator instead of assuming `Circuit.eval` is linear.
- Dependent gate indices and proof-carrying acyclicity should not leak into every
  simulation lemma.
- Raw initialization and formula fragments require a nonempty existing-wire
  prefix for constant gates. The canonical `T + n = 0` case must use the
  circuit-family empty-input branch or reserve a dummy primary wire.
- Arora--Barak count input vertices and explicit NOT gates, unlike the library's
  exact size convention. Prove additive/linear simulations before transporting
  exact `SIZE` bounds or claiming basis invariance; polynomial-size `PPoly` is
  insensitive to those overheads.

**Small entry tasks.**

- [x] Package a well-formed raw circuit as a typed `Circuit` if a later proof
  needs the reverse bridge; the executable evaluator itself does not require it.
- [x] Compile Boolean formulas into appendable raw fragments with exact size,
  topology, prefix-preservation, and evaluation laws.
- [x] Batch-compile Boolean formulas and pack their results into a contiguous
  block suitable for the next encoded configuration.
- [x] Define the bounded one-hot configuration layout used by functional
  unrolling and compile the initial configuration as an exact-size raw fragment.
- [x] Hardwire an arbitrary prefix of typed-circuit inputs without increasing
  the circuit size, retaining a positive live suffix under the typed-circuit
  convention (families handle length zero separately).
- [x] Implement a DTM realizing the topological memoized evaluator for serialized
  circuits and prove a polynomial running-time bound.
- [x] Define polynomial advice and basic monotonicity/containment lemmas,
  including `PAdvice_subset_PPoly` by double hardwiring.
- [x] Compile one fixed transition layer into a Boolean circuit as a local
  precursor to full unrolling, with exact packed semantics and a quadratic size
  bound in the trace horizon.
- [x] Tile initialization with one transition fragment per bounded choice,
  proving exact final-configuration semantics, topology, and a cubic size bound.
- [x] Append the final halt-and-output acceptance gate and package the resulting
  well-formed raw fragment as a typed single-output circuit.

### M2. BPP is contained in P/poly

**Goal.** Prove the classical nonuniform derandomization theorem
`BPP subset P/poly` using amplification and the probabilistic method.

**Prerequisites.** N2 amplification, M1 circuit-family acceptance unrolling and
hardwiring, and the PTM all-paths-halting discipline already present in the library.

**Target theorem variant.** Start with the library's concrete `BPP` definition and
the circuit-family definition of `P/poly`. The proof should not claim a uniform
derandomization. The fixed advice/random tape may depend on the input length but
not on the individual input.

**Staged milestones.**

- [x] Use the explicit completeness `2/3` and soundness `1/3` already built into
  the library's concrete `BPP` definition; no constant-normalization layer is needed.
- [x] Construct repeated independent runs and majority output with error below
  `2^-(n+1)` on each input of length `n`.
- [x] Prove by a union bound over all `2^n` inputs that some single random string is
  correct for every input of that length
  (`NTM.exists_uniform_correct_seed`).
- [x] Hardwire that string into the amplified acceptance circuit for length `n`
  (`CircuitUnrolling.fixedSeedAmplifiedAcceptanceCircuit` and
  `NTM.hardwiredAmplificationFamily`).
- [x] Prove the resulting family has polynomial size and conclude
  `BPP subset P/poly` (`BPP_subset_PPoly`; if the BPP time witness is
  `O(n^d)`, `NTM.hardwiredAmplificationFamily_size_bigO` gives size
  `O(n^(3d+4))`).
- [x] Derive the advice-TM formulation as a corollary
  (`PPoly_subset_PAdvice` and `BPP_subset_PAdvice`) using canonical serialized
  family-member codes as polynomial-length advice to the verified evaluator.

**Formalization hazards.** The amplified machine consumes a length-dependent
number of random bits, and early halting must not change the block layout. A strict
inequality below `1/2^n` is needed to conclude that the number of bad seeds is less
than the total number of seeds. Majority ties require an odd repetition count.
Hardwiring must preserve the exact acceptance bit, not merely the existence of an
accepting NTM path. Do not obtain the nonuniform circuit by unrolling
`repeatAtTime`: its control state stores the entire vote vector, so its
finite-state cardinality is exponential in the repetition count. Compose copies
of the original machine's acceptance circuit and a threshold fragment instead.

**Small entry tasks.**

- [S] Define the bad-seed set for a fixed input and rewrite its cardinality in terms
  of `acceptCount`.
- [x] Enumerate all `BitString n` inputs and prove its cardinality is `2^n`
  (`card_finArrowBool`).
- [x] Prove the “expected bad inputs below one implies a perfect seed exists”
  counting lemma independently of machines
  (`Complexitylib.Classes.FiniteCounting.exists_good_seed`).
- [x] Prove block independence, in exact-counting form
  (`Complexitylib.Classes.FiniteCounting.card_filter_block`, via `blockEquiv`) and in
  probability form (`Complexitylib.Classes.EventProb.eventProb_block`): a
  prefix/suffix-separable event's probability is the product of the two block
  probabilities. The core for relating a repeated machine's acceptance to its single
  run (`k` independent runs multiply their success probabilities).
- [x] Define a PTM repetition wrapper with an explicit choice-block schedule
  (`NTM.repeatAtTime`) and prove its compact-seed acceptance semantics.
- [x] Add a circuit/advice hardwiring operation and prove evaluation correctness
  (`Circuit.restrictPrefix`, with exact size preservation).
- [x] Compile an at-least threshold over existing verdict wires as an appendable
  quadratic-size raw fragment, ready for strict-majority amplification.
- [x] Compose independent copies of the original machine's bounded acceptance
  circuit over shared data and disjoint choice blocks, append strict majority,
  and prove exact `blockMajority` semantics with size
  `runs * O((T + 2)^3) + O(runs^2)`.

### M3. Small-depth circuits and Barrington's theorem

**Goal.** Develop robust `NC^1` infrastructure and prove Barrington's width-5
branching-program characterization.

**Prerequisites.** M1 circuit families and depth, finite group/permutation support
from Mathlib, and basic formula/circuit compilation.

**Target theorem variants.** The first technically clean result should be the
finite theorem:

> A fan-in-two Boolean formula of depth `d` can be computed by a width-5
> permutation branching program of length at most `4^d`.

From this, depth `O(log n)` gives polynomial length. A full class equality also
needs the converse simulation of constant-width polynomial-length branching
programs by log-depth circuits and a clearly stated uniformity convention.

**Staged milestones.**

- [x] Define Boolean formulas with literals, depth, evaluation, and compilation
  from a selected circuit output by recursively unfolding its DAG. (`BoolFormula`
  has variables/constants, literal helpers, evaluation, size, leaves, depth, and
  variable locality. `Circuit.outputFormula` recursively unfolds one selected
  fan-in-two output; `Circuit.eval_outputFormula` proves exact semantics, and
  `Circuit.depth_outputFormula_le_outputDepth` bounds its formula depth by twice
  the selected circuit-output depth. DAG sharing is intentionally duplicated, so
  no formula-size bound is claimed.)
- [x] Define width-`w` permutation branching programs: instructions selected by
  one input bit, ordered product semantics, length, and acceptance convention.
  (`Circuits/BranchingProgram.lean`: `BPInstr`, `BP`, `eval`, `eval_append`,
  `eval_cons`, `eval_rename`.)
- [x] Specialize to permutations of `Fin 5` and prove the explicit conjugation and
  commutator identities used by Barrington's induction. (Abstract core done in
  `Circuits/Barrington.lean`: `BP.inverse`/`eval_inverse`, the representation
  predicate `BP.Computes`, and the closure lemmas `Computes_conj`,
  `Computes_not`, and `Computes_and` — the commutator trick `⁅σ, τ⁆` for the AND
  gate — hold at any width. The `S₅` input is now proven in
  `Circuits/BarringtonS5.lean`: `exists_fiveCycle_commutator` exhibits two
  `5`-cycles (`finRotate 5` and `(0 2 4 3 1)`) whose commutator is again a
  `5`-cycle — verified by kernel `decide` (0 axioms, no `native_decide`) — and
  `every_fiveCycle_is_commutator` upgrades this to *every* `5`-cycle via the
  single-conjugacy-class fact (`isConj_iff_cycleType_eq`) plus conjugation
  distributing over `⁅·,·⁆`. So the full `S₅` target-cycle freedom Barrington's
  induction consumes is proven. `BPInstr.conjugate` and `BP.conjugate` now realize
  conjugation pointwise, preserving program length exactly.)
- [x] Compile literals and negation, then the AND/OR induction, tracking target
  cycles and a length bound. (The abstract move-set is functionally complete in
  `Circuits/Barrington.lean`: base cases `Computes_false`, `Computes_true`,
  `Computes_var` (literals), negation `Computes_not`, AND `Computes_and`, OR
  `Computes_or` (De Morgan). `Circuits/BarringtonBridge.lean` joins these to the
  `S₅` algebra: `BP.Computes_retarget` re-aims a program to any target `5`-cycle,
  and `BP.Computes_and5` gives the `AND` gate with full target-cycle freedom. The
  full formula recursion is done in `Circuits/BarringtonRepr.lean`
  (`Computes_formula`). `Circuits/BarringtonLength.lean` now adds pointwise
  length-preserving retargeting, compact negation with length `max 1`, and the
  exact four-copy commutator recurrence; `Computes_formula_depth_four` proves the
  tight `≤ 4 ^ depth` induction.)
- [x] State and prove the finite Barrington theorem. (Representation form
  **proven**: `Circuits/BarringtonRepr.lean` `barrington_representation` — every
  Boolean formula is computed by a width-`5` permutation branching program (some
  nonidentity `σ ∈ S₅` with program-value `= σ ↔ φ` true).
  `Circuits/BarringtonLength.lean` adds the textbook finite theorem
  `barrington_representation_depth_four` (`≤ 4 ^ depth`) and
  `barrington_quadratic_of_log_depth` — a formula of depth `≤ log₂ n` compiles
  to a width-`5` program of length `≤ n²`. The earlier `13 ^ size`, `17 ^ depth`,
  and `n⁵` statements remain compatibility corollaries. All 0 custom axioms.)
- [x] Lift it to nonuniform `NC^1`; then prove the converse by balanced composition
  of constant-size permutation transition matrices/functions. (Forward direction:
  `Circuits/BarringtonFamily.lean`
  `FormulaFamily.logDepth_polyLength_bp` — a logarithmic-depth (`NC¹`) formula family
  is computed formula-by-formula by a family of width-`5` branching programs of
  polynomial length `4^c·(n+1)^(2c)`. Converse and equality:
  `Circuits/BarringtonConverse.lean` — `BP.reachesFormula` composes two half-programs
  through the five possible intermediate states, `BP.depth_decisionFormula_le`
  bounds decision depth by `6·⌈log₂ length⌉ + 2`, and
  `barrington_equivalence` proves `FormulaNC1 = Width5BP`. All 0 custom axioms.
  The typed-family bridge is also complete:
  `BoolFunFamily.onTotalAssignments_mem_Width5BP` unfolds any `NC1` circuit
  family output with at most a factor-two depth increase and applies the
  Barrington equivalence. No formula-size claim is used.)
- [~] Add a uniform version only after instruction-generation uniformity is
  formalized. The extraction prerequisite is now complete:
  `Circuits/BarringtonCompiler` replaces proof-level conjugator choices by a
  computable enumeration of `S₅` and exposes an explicit recursive
  `barringtonCompile` with exact semantics and length `≤ 4 ^ depth`.
  `Circuits/BranchingProgramEncoding` now supplies the canonical machine-facing
  codec: fixed seven-bit `S₅` ranks, self-delimiting instructions/programs,
  exact decoding, injectivity, and explicit code-length bounds.
  `Circuits/FormulaEncoding` supplies the corresponding iterative postfix input
  format, and `Circuits/BarringtonCodeGenerator` fixes the total bitstring
  transformer `barringtonCompileCode`, proving generated-code decoding, exact
  formula semantics, the `4 ^ depth` instruction bound, and serialized length
  at most `4^depth + 1 + 4^depth * (inputCodeLength + 15)`. The remaining steps
  are a verified total log-space generator that agrees with this reference on
  a promised logarithmic-depth family, plus the resulting uniform family-level
  lift. The unbounded reference itself is not an `FL` candidate: arbitrary
  linear-depth inputs can require exponentially long output.
  `Classes/BarringtonUniform` now formalizes the correct promise-family boundary:
  canonical `FL` generators define `FormulaFamily.Uniform` and
  `BPFamily.Uniform`, the concrete `FormulaFamily.barringtonProgram` has fixed
  decision point zero, exact semantics, and polynomial length. The machine
  resource prerequisites now also expose that every `FL` output has a
  pointwise polynomial length bound with logarithmic-width indices, and prove
  that the *complete serialized code* of the concrete Barrington family
  (including terminated-unary variable fields) is polynomially bounded with
  logarithmic-width cursors. Thus the remaining construction may use
  recomputation and binary output positions without hiding a space blowup.
  `Models/TuringMachine/OutputCursor` now supplies the machine-level simulation
  kernel for that construction: `OutputCursor` quotients an append-only output
  prefix to finite control, exact step and run commutation are proved, and the
  executable `suppressOutputTM` retains the source input/work behavior while
  keeping its physical output empty. Its bounded-time computation theorem
  includes the final normalization seam. Observed cursor runs now count output
  advances exactly, including the theorem that the accumulated count from an
  initial configuration equals the final physical output-head position.
  `Models/TuringMachine/OutputProbe` adds the executable binary
  position/capture controller: non-right source steps preserve its extra
  countdown tape, right steps invoke the verified little-endian predecessor,
  and a finite start-marker mask normalizes and exactly restores any source
  heads parked on `▷` around that subroutine. Whole observed cursor runs now
  consume exactly their counted output advances, and a halted source on the
  selected Boolean frontier cell reaches the probe halt state with that
  one-bit physical output. The companion theorem covers cells finalized by an
  earlier right move, so the semantic capture cases are complete. Every prefix
  of a complete replay now stays within the source invariant's space plus the
  largest countdown's binary width, without accumulating predecessor costs.
  Canonical blank-output specializations also discharge the probe's physical
  head-and-cells premises after every positive-length replay.
  Output-frontier monotonicity and exact crossing now combine those two capture
  cases into one machine theorem for every valid index of a completed
  space-bounded transducer output. A generic post-sentinel wrapper now turns
  that result into a restartable query interface whose input, scratch,
  countdown, and physical-output tapes all enter parked at cell one. The
  output-retargeted form places the captured bit on a fresh work tape while
  preserving a parked blank real output, so repeated queries can compose
  without replaying the enclosing machine's sentinel transition. Successful
  valid-index queries now carry the replay bound through the two capture
  transitions, the restart wrapper, and output retargeting, including the
  fresh work tape that stores the selected bit; the controller can therefore
  cite one all-prefix space certificate for each complete query phase.
  `Circuits/BarringtonStreaming` now replaces complete program construction by
  a target-independent exact instruction-count recurrence and random-access
  instruction stream, with every query proved equal to the reference compiler.
  `Circuits/BarringtonSlots` schedules that same exact program inside `4^D`
  optional fixed-address slots for any promised depth bound `D`: erasing empty
  slots recovers the reference compiler byte-for-byte, and counting occupied
  slots recovers its exact instruction count. This removes recursive child-
  length arithmetic from the machine controller while keeping its output
  unchanged. `Circuits/BarringtonSlotQuery` now gives target-independent
  structural recurrences for the first and last occupied addresses and a
  direct query that follows only the selected base-four block; every queried
  slot is proved equal to the list-valued fixed schedule, including the
  inverse-block and postmultiplication transformations used by negation,
  conjunction, and disjunction.
  `FormulaEncoding/Navigation` supplies its stack-free postfix tree primitive:
  a backwards owed-subtree scan recovers exact child spans using one cursor and
  one counter. `Circuits/BarringtonTokenQuery` now lifts the direct fixed-slot
  recurrence from inductive formulas to canonical postfix token streams:
  binary child spans are recovered by that backwards scan, and every token-
  stream query is proved equal to the reference compiler's selected
  instruction. `FormulaEncoding/BitNavigation` now implements exact random
  access and subtree scans over the canonical framed bits themselves, including
  child-span recovery inside arbitrary token context. `BarringtonBitQuery`
  follows the selected base-four address directly over those bits and proves
  every result equals the fixed-slot compiler. `BarringtonBitSerializer` fixes
  the complete two-pass output algorithm: scan all `4^D` addresses to obtain
  the exact instruction count, then erase empty addresses and emit the canonical
  program code; under the promised depth bound its output is byte-for-byte the
  executable Barrington compiler's code. `FormulaEncoding/ProbeNavigation`
  replaces the in-memory code by a position-indexed bit oracle with total
  finite-fuel decoders and exact token/subtree/child-span correctness.
  `BarringtonProbeQuery` then proves that first/last occupancy and every direct
  fixed-address instruction query through that oracle agree with the reference
  compiler. Its machine-facing query has now also been factored through a
  target-free Boolean occupancy kernel: bounded scans over exactly `4^D`
  addresses recover the first and last occupied slots, and substituting those
  scans into every postmultiplication site preserves each queried instruction
  exactly. This removes nested recursive first/last evaluation from the
  serializer controller. `BPInstrTransform` now packages every pending inverse
  and postmultiplication of a selected instruction as an explicit finite type:
  both permutation branches undergo one shared `left * p^(±1) * right` map,
  while the unbounded variable index is preserved. Thus recursive descent need
  not store a transformation stack on work tapes.
  `Models/TuringMachine/Subroutines/BlankWorkPrefix` now supplies the
  missing replay-reset primitive: it blanks an arbitrary sparse work prefix
  bounded by a preserved binary limit, rewinds the target from an arbitrary
  in-bound head position, restores its scratch counter, and proves exact time
  plus an all-prefix space envelope. `BlankWorkPrefixMany` serially applies that
  primitive to a fixed sparse tape list without multiplying the peak-space
  bound. Successful output probes now also expose that their countdown ends as
  the canonical zero tape, including after restart, output retargeting, and
  placement in a larger controller frame, and give an exact blank-support bound
  for every query-owned tape. `OutputProbeCleanup` combines an exact-space input
  rewind with the fixed-list reset to restore the source, countdown, and
  capture tapes while preserving the controller frame. `OutputProbeConsume`
  now supplies the concrete restartable controller step: it reads the captured
  bit before
  cleanup, restores the exact canonical frame, dispatches to the matching
  continuation, and carries an explicit all-prefix space maximum through the
  whole query-consume-reset sequence. `OutputProbeLatch` now turns that
  finite-control result into a reusable canonical binary zero-or-one latch
  after cleanup while preserving an arbitrary outer serializer frame.
  Output probes are now total at every positive numeric position: the complete
  source run is split into crossed, final-frontier, and beyond-frontier cases,
  blank or absent positions emit canonical zero, and every branch retains the
  source-space-plus-binary-index all-prefix bound. Valid indices keep the
  stronger theorem identifying the emitted bit with the source function. This
  totality now passes through arbitrary real-output and controller frames,
  consume/reset, and the persistent canonical bit latch, so bounded serializer
  loops no longer need a valid-index side condition at each oracle query.
  `OutputProbeIndexed` now bridges the remaining ghost-index boundary: it
  copies a preserved zero-based controller register into the private probe
  countdown, increments to the probe's one-based convention, and composes that
  preparation with the total framed latch. The public contract preserves every
  non-countdown tape exactly and carries the combined all-prefix space bound,
  so `BinaryFor` clients can use a concrete machine register as their query
  address. `OutputProbeDispatch` now turns that persistent latch into a direct
  full-controller Boolean branch: valid indices select the exact source bit,
  parked frame seams are discharged once, and arbitrary zero/one continuations
  inherit a compositional time/space contract. Its resetting form now clears a
  true one-bit latch before the selected continuation, while the false branch
  reuses the already-canonical zero frame; both branches therefore reestablish
  the identical restart invariant with explicit clearing cost. This is the
  reusable iteration body boundary for the occupancy and serializer scans.
  The bounded-runtime `BinaryForSegmentSpec` and its all-prefix companion have
  now moved from the experimental routine adapter to the public `BinaryFor`
  API, so source-dependent probe runtimes can be selected existentially per
  address while remaining under one advertised loop bound. Its canonical
  witness adapter now packages those existential Hoare runs without repeated
  choice plumbing. The matching initial-bound adapter now turns canonical
  comparison/iteration entry bounds plus runtime reserve into the full
  all-prefix `BinaryForSegmentSpaceSpec`, without replaying phase semantics.
  `OutputProbeScan` performs the concrete machine wiring:
  it embeds address and limit registers behind the probe frame, queries and
  resets the latch, runs the selected continuation, increments the address,
  and preserves one-way output safety through the complete bounded scan.
  `OutputProbeCountOnes` now supplies the serializer's first-pass branch body:
  a zero probe preserves the complete reset-latch frame, while a one probe
  increments exactly one canonical binary count register. The composed
  query-reset-count step has an explicit time/space contract and the enclosing
  count-up scan remains one-way-output safe. Its exact outer-loop invariant is
  now formalized as well: after address `k`, the count register contains the
  number of true bits in the first `k` source positions. Canonical restored
  latch frames make Hoare endpoints literal loop configurations, and bounded
  per-address body witnesses now package into a complete
  `BinaryForSegmentSpec`; the halted frame exposes `List.count true` when the
  scan limit is the full bit length. Those body witnesses are now derived
  directly from the source transducer's `ComputesInSpace` contract and the
  canonical restored frame: finite frame maxima discharge the concrete
  indexed-latch and branch seams, and noncomputably selected per-address
  runtimes assemble a complete exact-prefix segment certificate. The remaining
  first-pass resource proof is specifically to attach an all-prefix segment-
  space certificate with a bound suitable for the final logarithmic asymptotic
  argument. `OutputProbeDecodeNat` now starts the Barrington-specific formula
  query controller: it gives terminated-unary headers and variable fields a
  concrete bounded probe loop with cursor, accumulator, fuel, and persistent
  success registers. Its pure controller is proved exactly equal to the
  established oracle decoder, including fuel exhaustion, and the complete
  concrete machine is one-way-output safe. Its selected zero/one continuations
  now have literal restored-frame contracts, and a valid source address plus
  `ComputesInSpace` derives the complete active query/reset/update step without
  caller-supplied replay witnesses. The outer active-flag branch is now
  certified in both states and exposed through one source-derived body theorem
  whose post-frame follows the same finite-list bit as the pure decoder
  recurrence. The exact `BinaryFor` lift is now complete as well: an injective
  six-role controller layout supplies canonical comparison, iteration, and
  halted frames; source-derived per-query runtimes assemble a complete segment
  whose final registers are the pure decoder state at the fuel bound.
  `OutputProbeDecodeTag` now supplies the next controller layer's six-way pure
  classifier, a concrete three-probe machine, one-way-output safety, and an
  exact source-derived contract for each query/reset/retain/cursor step. Those
  three contracts now compose into one exact run whose literal final frame
  retains all three source bits and advances the cursor by exactly three. A
  direct controller-symbol tree now dispatches that frame to all six legal
  continuations or the reserved-tag failure branch, and the combined theorem
  composes source-derived probing and exact two- or three-step dispatch in one
  run. `OutputProbeDecodeToken` now gives the tag and terminated-unary layers
  one injective nine-role controller layout with definitionally shared cursor
  and scratch registers. Its exact cleanup phase resets all three retained tag
  bits to a canonical zero frame without changing any other controller tape;
  invariant-restoring dispatch now wraps every legal and invalid continuation
  in that same cleanup contract. Selected-continuation variants of both the
  retained-tag and normalized-token contracts require only the branch that can
  actually execute, so constant tokens do not inherit an impossible variable-
  payload precondition. The source-derived token theorem now composes all three
  probes, tag retention, canonical cleanup, and selected dispatch in one exact
  machine run. The variable branch is now instantiated concretely by the
  bounded terminated-unary machine through the shared layout. The generic
  `BinaryForSegmentSpec.hoareTime` adapter and the source-derived
  `ComputesInSpace.outputProbeDecodeNatTM_hoareTime` theorem now expose that
  complete loop between canonical initialized and final latch frames.
  `ComputesInSpace.outputProbeDecodeTokenVar_hoareTime` now transports the
  normalized post-tag frame into that canonical unary start frame and certifies
  the concrete variable continuation. `BranchingProgramEncoding/Machine` now
  supplies the serializer leaf itself: it emits a dynamic terminated-unary
  variable field followed by two finite-control permutation ranks, restores the
  complete input/work frame, and carries explicit time, all-prefix space, and
  one-way-output contracts. Constant and variable Barrington instructions are
  exposed as direct specializations. A restored-latch adapter now transports
  those emitters through the complete restartable-query frame, and
  `outputProbeDecodeVarInstrTM_hoareTime` certifies the whole normalized
  `.var` continuation from bounded payload decoding through exact instruction
  emission. The leaf dispatcher is concrete as well: `.tru` uses the constant
  emitter, `.fls` uses the certified no-output frame adapter, and only the
  recursive connective continuations remain parameters. A generic selected-
  branch contract exposes that exact machine boundary without demanding proofs
  for unreachable leaf or recursive branches. Its three source-level leaf
  contracts are now certified end to end: `.var` alone assumes and decodes a
  bounded terminated-unary payload before appending the exact dynamic
  instruction, `.tru` appends the exact constant instruction without a payload
  assumption, and `.fls` preserves the accumulator unchanged. The next local
  seam is the recursive address/navigation controller for `.neg`, `.conj`, and
  `.disj`. Its numeric state is now stack-free: `BarringtonSlotCursor` keeps the
  original fixed address plus one reflection bit, splits each effective address
  into its current base-four block and remaining local slot, and toggles only
  that bit when descent enters an inverse block. Its branch equations identify
  right-child and inverse-block selection with the two corresponding binary
  address bits xor that reflection flag. The four-way machine dispatcher over
  two captured canonical bit tapes is now concrete, costs exactly two framed
  transitions beyond its selected continuation, preserves the continuation's
  all-prefix space budget, and is one-way on output. Its raw-bit continuation
  is proved equal to the cursor's semantic branch. A one-transition capture
  primitive now canonicalizes the currently positioned source bit, optionally
  moves the preserved address head left, carries an all-prefix space contract,
  and is one-way on output. Its three-transition high/low composition captures
  one adjacent base-four digit, leaves the source on the low bit, preserves all
  unrelated tapes, carries its own all-prefix space contract, and remains one-
  way on output. The runtime positioner is now concrete as a canonical binary
  count-up loop whose certified two-transition body advances one base-four
  digit, followed by a certified one-transition move onto the current high bit;
  its exact loop invariant identifies iteration `v` with head offset `2 * v`.
  The complete positioner lands on bit `2 * fuel + 1`, preserves the address
  cells, advances its canonical counter exactly to `fuel`, and carries the
  all-prefix bound `initialSpace + 2 * fuel + 2 * fuel.size + 6` rather than a
  time-derived quadratic bound. Positioned canonical cells are also proved to
  expose exactly `Nat.testBit`, including implicit blank high bits. Positioning
  and the three-transition adjacent-bit capture now compose into one public
  exact contract, and the resulting raw bits feed the four-way dispatcher and
  any selected continuation. The end-to-end branch retains the tight
  positioning-plus-three all-prefix budget, adds exactly the two dispatch
  transitions, and remains one-way on output. The cursor-facing theorem hides
  the raw-bit arithmetic behind the semantic left/right/inverse choice. After
  this one-time positioning phase, recursive slot descent no longer rescans
  from the address origin: one transition moves onto the next lower digit and
  simultaneously resets both bit latches, then the existing three-transition
  capture and two-transition dispatcher select the next semantic child. This
  constant-cost recursive step has an explicit all-prefix bound and preserves
  one-way output behavior. Postfix child navigation now also has a forward-
  streaming invariant tailored to the existing token decoder: scanning a
  binary root's child body maintains only the evaluation-stack height and the
  most recent height-one boundary. That boundary is proved to be exactly the
  end of the left child in both token count and encoded-bit offset, eliminating
  repeated backward ordinal seeks. The machine-side numeric step is now
  concrete as well: eight distinct binary registers hold the cursor, stack
  height, token count, retained boundaries, constant one, verdict, and copy
  scratch. One certified call applies the token arity, increments the token
  count, performs normalized binary equality, conditionally copies both
  boundaries, restores scratch, and preserves one-way output behavior. The
  numeric step is now wrapped around the existing fixed-tag/terminated-unary
  token decoder by an injective sixteen-role controller layout. The decoder and
  scan share exactly the source cursor; every other register is structurally
  disjoint. The concrete dispatcher maps variables, constants, negation, and
  both binary connectives to arities zero, zero, one, and two respectively. A
  completed variable decoder now has a certified normalization phase that
  clears its value and loop counter, restores its active flag, preserves the
  complete numeric scan frame literally, and remains one-way on output.
  Source-derived one-token contracts now cover both sides of the dispatcher:
  every legal fixed token maps through one tag-to-arity theorem, while a
  variable composes bounded payload probing, the pure decoder's terminal
  cursor/value state, normalization, and the arity-zero update. The numeric
  scan invariant now transports automatically into restored latch frames,
  through fixed-tag cleanup, and through the variable decoder's cursor update;
  source theorems need only the original stable scan frame. Canonical variable
  encodings also have an exact successful decoder result with arbitrary extra
  fuel, exposing the post-token cursor and terminated active state. The bounded
  scan now has its own injective eighteen-role layout and concrete count-up
  wrapper: the first sixteen roles project to the complete token step, while a
  fresh iteration counter and preserved token limit are certified distinct
  from every token role. This avoids aliasing the loop counter with the
  semantic token count already incremented by the body. The next seam is the
  stream-indexed loop invariant for that wrapper, followed by the
  finite-control cursor/transform updates.
  `BarringtonProbeSerializer` fixes the complete oracle-level two-pass output
  and proves that its counted header, filtered instruction stream, and final
  code agree byte-for-byte with the executable compiler. The remaining
  construction is to iterate these latched controller steps through the oracle
  recurrences and the two serializer scans, together with the resulting
  logarithmic-space proof.
  Finally,
  `uniformFormulaNC1_subset_uniformWidth5BP_of_compilation` reduces the forward
  uniform theorem to the single named obligation
  `UniformBarringtonCompilation`. Proving that obligation is the remaining
  machine-level work.

**Formalization hazards.** Permutation multiplication order differs between texts
and libraries; fix it with executable examples before proving the induction.
Barrington's theorem is not true for arbitrary width-5 monoid programs without the
specific non-solvable group construction. The formula-to-program theorem and the
class-level circuit theorem are distinct, and sharing in a circuit must be handled
without an unjustified formula-size claim.

**Small entry tasks.**

- [x] Define branching-program evaluation and prove append/product semantics
  (`Complexitylib.Circuits.BranchingProgram`: `BPInstr`, `BP`, `BP.eval`,
  `BP.eval_append`, `BP.eval_cons`).
- [x] Encode a program instruction and prove evaluation is invariant under a
  semantics-preserving rename of input variables (`BPInstr.rename`, `BP.rename`,
  `BP.eval_rename` in `Complexitylib.Circuits.BranchingProgram`).
- [x] Verify concrete `S_5` permutations with the required commutator identity
      (`exists_fiveCycle_commutator`, kernel `decide`, no `native_decide`).
- [x] Implement literal and NOT programs with exact length bounds
      (`Computes_var`, `Computes_not`, `Computes_formula_len`).
- [x] Prove balanced product evaluation has logarithmic formula depth for fixed
      width (`BP.depth_reachesFormula_le`, `BP.depth_decisionFormula_le`).

### M4. Space complexity, alternation, and QBF

**Goal.** Supply the space and alternation results needed by oracle and interactive
proof tracks.

**Prerequisites.** N1 encodings, existing auxiliary-space semantics, and N3 QBF
syntax.

**Staged milestones.**

- [ ] Prove closure and normal-form lemmas for deterministic and nondeterministic
  space, including configuration counting.
- [ ] Formalize Savitch's theorem with an explicit recursive reachability machine:
  `NSPACE(S) subset DSPACE(S^2)` under suitable constructibility and lower-bound
  hypotheses.
- [ ] Derive `NPSPACE = PSPACE` in the library's polynomial-union convention.
- [ ] Define alternating machines or an equivalent bounded game semantics.
- [ ] Prove polynomial-time alternation equals PSPACE, or first prove a bounded
  configuration-game characterization.
- [ ] Prove TQBF is PSPACE-complete.
- [ ] Add deterministic and nondeterministic space hierarchy theorems with exact
  constructibility assumptions.

**Formalization hazards.** Space bounds do not automatically bound time unless
configurations are finite and repetitions are removed. The library's output tape
is excluded from space, so transducer restrictions matter. Savitch's recursion
needs careful termination and an encoded midpoint enumeration whose own workspace
is accounted for.

**Small entry tasks.**

- [S] Define bounded configurations and prove they form a finite type after tapes
  are truncated to the relevant cells.
- [M] Bound the number of bounded configurations in terms of state count, tape
  count, and space.
- [x] Define QBF evaluation and prove elementary substitution lemmas
  (`Complexitylib.SAT.QBF`: `QBF.eval`, `eval_ex_iff`, `eval_all_iff`).
- [M] Implement the recursive reachability predicate before implementing its TM.

### M5. Interactive-proof foundations

**Goal.** Define interactive protocols in a way that supports both finite
information-theoretic soundness proofs and polynomial-time complexity classes.

**Prerequisites.** N1 transcript codecs, N2 finite probability, and eventually M4
for the `IP = PSPACE` endpoint.

**Definitions to settle first.**

- A fixed-round protocol with bounded prover/verifier messages.
- An unbounded prover strategy as a function of the visible transcript.
- A verifier with private random bits and explicit work/time bounds.
- Completeness and soundness quantified over inputs and prover strategies.
- Public-coin protocols as a separate restriction, not the default semantics.

Start with fixed finite alphabets and rational probabilities. Only then package
families of protocols with polynomial bounds into `IP`, `AM`, and related classes.

**Staged milestones.**

- [ ] Define transcripts, legal interaction, deterministic prover strategies, and
  verifier acceptance counts.
- [ ] Prove strategy extensionality: only responses on reachable transcripts
  affect acceptance.
- [ ] Define completeness/soundness and prove monotonicity in thresholds.
- [ ] Formalize sequential repetition and one soundness-amplification theorem.
- [ ] Define polynomially bounded protocol families and `IP`.
- [ ] Prove elementary containments such as `NP subset IP` and
  `IP subset EXP` before attempting the sharp upper bound.

**Formalization hazards.** A prover is adaptive, so it cannot be represented by a
single witness string without encoding a potentially exponential strategy tree.
The verifier's private coins must not be exposed in the prover's transcript.
Message-length bounds are essential to keep the strategy space finite for counting
and exhaustive-search upper bounds.

**Small entry tasks.**

- [S] Define alternating transcript extension and prove prefix/round-index lemmas.
- [S] Define acceptance probability for a fixed prover and verifier random tape.
- [M] Embed an NP verifier as a one-message interactive protocol.
- [M] Prove that deterministic prover strategies suffice for maximizing acceptance
  in the finite classical model.

### M6. Random access machines and machine-model robustness

**Goal.** Relate the Turing-machine model to a Random Access Machine (RAM) — a
register machine with indirect addressing — so that the polynomial-time and
polynomial-space classes are provably model-independent, and so later
algorithm-design work has an honest cost model closer to real computation.

**Prerequisites.** The core Turing-machine model and its time/space predicates,
N0 run/time-accounting lemmas, and the multi-tape → single-tape simulation.

**Current progress.** The model is defined in
`Complexitylib.Models.RandomAccessMachine`: an instruction set with immediate,
`add`/`sub`/`mul`, indirect `load`/`store`, and jumps; an executable step and
fuel-bounded run; a **logarithmic-cost** time measure charging each instruction
the bit-length of the numbers it manipulates; a matching space measure; and the
classes `RAM.DTIME`, `RAM.DSPACE`, and `RAM.P` over the shared `Language`
interface. The
operational metatheory (run/cost additivity, stationarity after halt, monotonic
cost, step count `≤` log time, finite register support) is proved. The **cost
convention is justified by a theorem**, `RAM.logGap_squaring`: the squaring
program family runs in unit time `k + 1` but logarithmic time at least `2 ^ k`,
so a unit-cost measure would make the RAM super-polynomially stronger than a
Turing machine. This settles the model, its resource conventions, and its
soundness. A minimal structured imperative frontend now compiles source-level
sequencing, conditionals, and loops to flat RAM code with exact semantic,
logarithmic-time, and peak-space preservation; its verified Hamming-weight
program is the first end-to-end algorithm benchmark, with exact step count and
explicit quasilinear logarithmic-time and peak-space bounds. Reusable internal
resource certificates discharge finite-store, basic-instruction, branch, and
loop accounting without enlarging the public trusted surface. The machine-model
simulation now has its first representation layer: `RAM.TMConfig` assigns
explicit contiguous state, named-head, and bounded-cell register blocks, uses
zero for blank cells, proves exact field lookup and decode-after-encode for
configurations blank beyond the chosen window, and proves every register beyond
the layout is zero. The next fixed-block layers are also checked: a decrementing
finite numeric switch selects a branch with exact source/compiled steps and
explicit cost/space envelopes, and the generated transition prelude preserves
the represented configuration while loading its state and all named head
symbols exactly. The statically selected transition action is now also checked:
its generated straight-line operations preserve the scratch frame, implement
the input/work/output head moves and writes exactly, and re-establish the full
configuration representation for the TM successor. The nested state-and-symbol
dispatch, common logarithmic-cost/space envelope, and compiled-RAM transfer are
now composed as well: the complete dense structured block has an exact source
execution count, compiles with concrete resource bounds, represents the TM
successor, and decodes to it when the successor fits the chosen window.

An important uniformity audit found that this dense block is a bounded program
family: its register layout and generated program depend on the tape window.
It is therefore a useful end-to-end compiler validation but cannot directly
witness `RAM.DTIME`, whose existential program must be fixed independently of
the input and resource bound. The uniform replacement has now begun with a
fixed sparse interleaved layout. Its complete unbounded representation and
decode/encode theorem are checked, and a program depending only on the TM now
computes current-cell addresses at runtime and loads the state and every named
head symbol exactly. The sparse selected actions and nested dispatch are now
checked as well, including exact transfer to concrete compiled RAM execution.
A fixed loop controller then follows any exact `TM.reachesIn` halting run,
preserves the complete sparse representation, reaches the compiler's terminal
halt instruction, and decodes to the exact halted TM configuration. The program
depends only on the TM, not on the input or its time bound. The public-ABI layer
is now checked end to end as well. Its finite branch tree remembers the six raw
input bits occupying scratch registers; its backward loop converts public bit
codes `0/1` to sparse symbol codes `1/2`, relocates every input cell, and records
visited captured destinations without a second marker tape; its conditional
repair distinguishes captured zero bits from positions beyond the input; and
its initialization establishes the complete sparse `tm.initCfg`. The fixed
decision program then follows any exact halting run and converts the halted
output symbol back to the public `R₀` verdict `0/1`, with exact source-to-
compiled register, logarithmic-cost, and peak-space preservation. Concrete and
asymptotic resource envelopes are now checked for the sparse simulation core:
one common store envelope survives every load, dispatch, write, continuation,
and loop iteration; a `t`-step run has cost at most
`(t + 1) * C_tm * wordWidth(tm, base + t)`; and `wordWidth` is formally
`O(log bound)`. Extending that envelope through the public marshaller and
verdict extractor is now checked as well: the fixed `compiledDecision` has a
single concrete cost bound depending only on the TM, input length, and simulated
step count, plus an explicit peak sparse-store bound, from raw public input to
the final `R₀` verdict. The transfer is now packaged at the class level:
`RAM.TMConfig.Sparse.P_subset_RAM_P` proves `P ⊆ RAM.P` by combining the
fixed simulator with the library's polynomial-time normal form and a checked
polynomial envelope for every ABI and simulation resource bound. The sharper
parametric `DTIME(T)` containment remains open because the public input
marshaller costs `O(n · log n)` and therefore needs an explicit hypothesis
relating input length to `T(n)`. Constructing the reverse RAM-to-TM simulation
has now begun at its representation boundary. `RAM.RegisterStore` materializes
every finite-support register file as a canonical list of nonzero address/value
pairs, gives words a self-delimiting binary tape code, proves exact codec
round trips, and bounds an `m`-entry width-`w` snapshot by
`(m + 1) * (4w + 2)` cells. Its finite sparse interpreter preserves
canonicality and decodes exactly to every RAM instruction and complete
fuel-bounded run. Entry count grows by at most the actual RAM step count, while
snapshot width grows only with fixed program literals and charged logarithmic
RAM time. Since actual step count is at most log time,
`RAM.RegisterStore.Snapshot.encode_run_length_le_logTime` gives an explicit
quadratic reachable-code envelope. The public ABI is included:
`Snapshot.initial_represents` gives a canonical sparse form of `RAM.initCfg`,
and `encode_initial_run_length_le_logTime` specializes the envelope to input
length and charged time. Concrete realization has now crossed its first machine
boundary: `RegisterStore.Machine.wordWidthTM` scans a word's unary width prefix,
stops on the zero separator, and produces the exact canonical binary width with
an exact framed runtime theorem; `payloadBitTM` consumes and appends one payload
bit in one proved transition. `wordPayloadTM` composes that leaf with the
canonical binary count-up driver. `wordDecodeTM` now composes the width scan,
separator step, and payload loop into a complete decoder: its canonical theorem
consumes one `WordCode.encode` prefix exactly, leaves the following stream
untouched, and supplies both an exact runtime and a coarse all-prefix
auxiliary-space envelope. The decoder deliberately leaves the target head at
its append position; `wordTargetRewind_reachesIn_frame` now converts that
payload to the canonical cell-one read convention in linear time while
preserving every framed tape. `TM.binaryEqTM` now compares two canonical binary
strings in linear time, writes the equality bit to a dedicated work tape, and
preserves the public output and every unrelated tape. `entryDecodeTM` now
composes two word decoders over seven pairwise-distinct tapes, consumes one
canonical `Entry.encode` prefix in exact time, recovers both address and value,
leaves the following entry stream untouched, and has an all-prefix auxiliary-
space envelope. `entryMatchTM` now composes the entry decoder and decoded-
address comparator over nine pairwise-distinct tapes, consuming one entry and
exposing its value and Boolean match flag with a parked frame and an explicit
time/space envelope. `entryMatchReadTM` rewinds that flag to cell one for direct
controller inspection while retaining every decoded scratch contract and an
explicit per-tape head bound.
`TM.resetBinaryWorkTM` now provides the reusable miss-reset leaf: from any
bounded positive cursor over canonical binary contents it rewinds and clears to
the standard blank tape with a literal frame and explicit time/space envelope.
`TM.resetBinaryWorkManyTM` composes that leaf across a fixed injective tape list.
The complete `entryScanTM` is now checked: one fixed controller reads a runtime
canonical binary entry count, decodes and compares entries in order, halts with
the first matching decoded value, or rewinds the query, clears all seven scratch
tapes, decrements the count, and continues. Its public contract certifies either
the first match or absence from the whole store, preserves every tape outside
the ten-tape assignment exactly, and supplies explicit time and all-prefix
space envelopes. The optimized decoder path is now integrated rather than only
bounded abstractly: `wordDecodeLinearTM` makes three unary-marker passes in
exactly `3w + 3` transitions, `entryMatchReadTime_eq` gives the resulting closed
linear match cost, and `entryScanTime_le_encoded` charges a complete scan by the
actual live entry encoding, repeated query width, and remaining-count term. The
lookup seam is now closed:
`entryLookupTM_hoareTime_frame` identifies the final
decoded-value tape with `RegisterStore.read`, including the default-zero miss
case, while retaining the scanner's exact external frame. Encoded update is the
next seam. Its reverse serialization dependency is now checked:
`wordEncodeTM` emits the exact self-delimiting word codec in two passes, and
`rewindEntryEncodeTM` rewinds arbitrary bounded decoded address/value cursors
and emits `Entry.encode` with explicit time, space, and literal frames.
`entryMissCopyTM` now appends one unmatched entry and restores the next-entry
scratch invariant with a deterministic intermediate work state.
`entryReplaceCleanupTM` now emits a matched address with a distinct canonical
new-value source, restores that source exactly, and clears the old decoded
entry. `entryAppendRestoreTM` handles the absent-address endpoint, emitting the
fresh entry and restoring both query and new-value sources exactly.
`entryUpdateTM` now closes the update seam: one fixed thirteen-tape controller
iterates comparison, miss-copy, replacement, deletion, absent-address append,
and both runtime counts. Its public contract realizes `RegisterStore.write`
with exact external frames and explicit time/all-prefix space envelopes.
The encoded source is also certified read-only and preserved literally across
lookup and update, with an arbitrary-start head-displacement bound available
for later cursor restoration. Width-efficient addition, truncated subtraction,
and multiplication now share one concrete arithmetic instruction ABI and feed
their result directly into the update replacement tape. The composed theorem
realizes the corresponding sparse-store write with an exact runtime and can
redirect the updated encoding to a fresh work tape while leaving the public
output blank. Reusable operand loading is now checked end to end as well:
`entryLookupLoadedTM` copies a canonical query into scanner storage, performs
the bounded lookup, rewinds and copies out the semantic value, resets all nine
scanner-owned binary tapes, rewinds the read-only encoded source, restores the
runtime entry count, and returns to the same blank-query ABI. Its public theorem
gives the exact sparse-store `read`, complete external frame, composed runtime,
transducer certificate, and all-prefix space envelope. The complete concrete
instruction simulator is now checked too: immediate, direct arithmetic,
indirect load/store, conditional and unconditional jumps, and halt share one
buffered endpoint; a canonical PC copy drives a fixed decrementing finite
dispatch tree; and `programInstructionTM_hoareTime_frame` realizes the exact
selected sparse snapshot step with an explicit runtime, transducer certificate,
and all-prefix space envelope. The reverse simulation is now complete at
polynomial-class granularity. A fixed twenty-work-tape machine marshals the
public input into the sparse snapshot ABI, iterates the exact instruction
simulator through the first halt, performs all cleanup and buffer swaps, and
extracts the RAM verdict. Its checked fourth-degree envelope depends only on
input length and charged RAM logarithmic time. Minimal halting fuel equals unit
time and is bounded by logarithmic cost, yielding
`RAM.RegisterStore.Machine.RAM_P_subset_P`; with the fixed sparse forward
simulator, `RAM.RegisterStore.Machine.RAM_P_eq_P` proves `RAM.P = P`. The sharp
parametric reverse bound is now checked as well: the optimized fixed machine
keeps the public input immutable, stores only a positive-tagged sparse mutable
overlay, charges each step by its selected instruction width, and sums those
charges with a decreasing square potential. This yields an explicit
`O((n + T(n))²)` public-ABI envelope and
`RAM.RegisterStore.Machine.RAM_DTIME_subset_DTIME_sq` under the necessary
input-domination hypothesis `n + 1 = O(T(n))`. The original fourth-degree
envelope remains available as the simpler fallback theorem.

**Settled conventions.**

- Register file `ℕ → ℕ`, with input length in `R₀` and bits in `R₁ … Rₙ`, and
  the decision verdict read back from `R₀`.
- Time is logarithmic cost, never unit cost; the `+ 1` base cost makes every
  step cost `≥ 1`. Direct register indices are program constants and not charged;
  runtime (indirect) addresses are charged their bit-length.
- Space is the peak, over the run, of the bit-length needed to name and store
  every nonzero register; finiteness of register support keeps it well defined.

**Staged milestones.**

- [x] Define the instruction set, executable semantics, and logarithmic time
  and space measures with explicit input/output conventions.
- [x] Prove the run/cost algebra, halting stationarity, and finite support.
- [x] Prove the unit-vs-logarithmic gap theorem justifying logarithmic cost.
- [x] Define `RAM.DTIME`/`RAM.DSPACE` and prove monotonicity in the bound.
- [x] Use one fixed sparse RAM program to simulate every polynomial-time
  multi-tape Turing decider, giving `P ⊆ RAM.P`.
- [ ] State and prove the sharper parametric forward containment, with the
  input-length domination hypothesis needed to absorb the ABI's
  `O(n · log n)` marshalling cost into `O(T(n) · log T(n))`.
- [x] Simulate every polynomial logarithmic-cost RAM decider by one fixed
  multi-tape Turing machine with an explicit polynomial envelope, giving
  `RAM.P ⊆ P`.
  - [x] Define the canonical finite address/value representation, binary tape
    codec, concrete length envelope, and semantics-preserving sparse
    instruction/run interpreter.
  - [x] Implement the exact unary-width scanner and framed one-bit payload-copy
    leaf for the concrete self-delimiting word decoder.
  - [x] Compose the payload leaf with a canonical binary counter and preserved
    width into an exact fixed-width payload loop.
  - [x] Compose the width and payload phases into a complete concrete word
    decoder with an explicit time/space bound.
  - [x] Establish a framed linear-time target rewind/read convention for
    decoded words.
  - [x] Implement a framed linear-time binary address comparator whose result
    lives on a work tape.
  - [x] Compose two complete word decoders into an exact framed sparse-entry
    decoder with an explicit time/space bound.
  - [x] Compose decoded-address rewind and work-tape equality with explicit
    time/space and left-marker preservation.
  - [x] Implement a framed rewind-and-clear primitive for resetting arbitrary
    canonical binary cursors after a lookup miss.
  - [x] Compose the entry decoder and decoded-address comparator into one
    framed decode-and-match unit with explicit time/space bounds and parked
    endpoint heads.
  - [x] Rewind the one-bit match result to a readable cell-one endpoint while
    preserving decoded scratch contracts and a per-tape head bound.
  - [x] Implement bounded sparse lookup/update on the encoded register-store
    tape.
    - [x] Implement the fixed runtime-count entry scanner, including direct
      hit branching, miss cleanup, first-match/absence semantics, exact frames,
      and explicit time/all-prefix space bounds.
    - [x] Package the scanner as lookup and prove its value tape equals the pure
      sparse-store `read`, including the default-zero miss case.
    - [x] Build encoded update behavior over the checked scanner endpoint.
      - [x] Emit exact self-delimiting words and entries from canonical or
        arbitrary bounded decoded cursors, with time/space and literal frames.
      - [x] Compose decoded-entry emission with scratch cleanup into an exact
        framed miss-copy branch that appends one unmatched entry and restores
        the next-entry invariant.
      - [x] Compose matched-address replacement emission, restoration of the
        external new-value source, and scratch cleanup with exact global frame.
      - [x] Emit a final absent-address entry from the query/new-value tapes and
        restore both source cursors exactly.
      - [x] Compose comparison, deletion, and runtime-count control around the
        checked copy/replacement/append branches.
  - [x] Compile the remaining sparse interpreter operations to a concrete
    multi-tape TM and prove the per-instruction scan and binary-arithmetic
    bounds.
    - [x] Add a finite-state ripple-carry machine for canonical addition that
      preserves both operands, writes a fresh sum, restores all three heads,
      and proves an exact framed runtime plus a linear bit-width envelope.
    - [x] Replace canonical copying's hidden value-counted addition with the
      width-linear ripple adder, and add an exact binary-work-tape loop with
      all-prefix space and transducer certificates for bit-driven algorithms.
    - [x] Add width-efficient truncated subtraction and multiplication.
    - [x] Compose the three arithmetic operations directly with encoded sparse
      update under one concrete tape ABI, exact framed runtime, source
      preservation, and redirected-output contract.
    - [x] Build a reusable loaded-operand lookup that restores scanner scratch,
      the encoded-source cursor, and the runtime entry count before returning.
    - [x] Compose arithmetic, lookup/update, control flow, and the one-step
      snapshot ABI into one concrete instruction simulator.
  - [x] Add exact cleanup and buffer-swap phases between simulated instructions.
  - [x] Marshal the public input into an initial sparse snapshot and extract the
    halted verdict through the public output ABI.
  - [x] Iterate the fixed instruction simulator through an arbitrary exact
    halting RAM run.
  - [x] Bound the complete simulator by a checked fourth-degree envelope in
    input length and charged RAM logarithmic time.
  - [x] Use least halting fuel to transfer polynomial RAM deciders to polynomial
    Turing deciders.
- [x] Sharpen the concrete reverse runtime to the textbook `O(T(n)^2)` bound and
  package the parametric `RAM.DTIME(T) ⊆ DTIME(T²)` containment under explicit
  input-length domination hypotheses.
  - [x] Replace the current product of entry count and maximum entry width with
    an amortized bound on the total live sparse-store encoding in terms of the
    public input and accumulated logarithmic RAM cost.
  - [x] Tighten the word decoder, entry match, and update accounting so a store
    scan is charged by the encoded data actually traversed; redesign any
    genuinely quadratic per-entry controller that prevents the target bound.
    - [x] Prove the existing checked word decoder is
      `O(w * bitlen w)`, replacing the former coarse `O(w²)` charge.
    - [x] Replace its repeated full-width binary comparison with a unary-marker
      payload pass so decoding is linear in the self-delimiting word code;
      thread it through entry matching, cleanup, lookup, update, and complete
      program execution, and expose an encoded-length scan theorem.
  - [x] Split the dense public-input bank from the mutable sparse overlay (or
    provide an equivalent lazy input ABI). The current eager snapshot code has
    a checked `O(n * bitlen n)` initialization term, which cannot be rescanned
    on every RAM step in a genuinely quadratic simulation under only `n ≤ T(n)`.
    - [x] Define and verify the pure positive-tag overlay semantics, including
      the one-entry initial snapshot, preservation under every instruction, and
      linear live-overlay growth over a run.
    - [x] Implement the concrete immutable-input fallback. A binary countdown
      scan returns `RAM.initRegs input address` in at most
      `n * (2 * bitlen address + 9) + 1` steps; the complete wrapper restores
      the input head and scratch tapes. `denseOverlayLookupTM` composes this
      fallback with sparse tagged lookup and proves exact `DenseOverlay.read`
      semantics at the existing reusable fourteen-tape boundary.
    - [x] Replace every instruction-kernel read with the dense-overlay lookup
      and successor-tag every data-instruction update value. Exact Hoare/time
      contracts now cover immediate, direct arithmetic, indirect load/store,
      and conditional-jump kernels while retaining the sparse fallback path.
    - [x] Replace eager initialization by the lone tagged `R₀` overlay entry,
      retaining and rewinding the immutable public input bank.
    - [x] Connect the dense instruction kernels through fixed-program dispatch,
      cleanup, looping, and final output.
  - [x] State a width-sensitive one-step simulation theorem using the selected
    instruction's actual charged operand widths, rather than assigning every
    instruction the run-wide maximum scale.
  - [x] Sum the per-step charges over a complete run to obtain an
    `O((n + T(n))^2)` public-ABI bound, then use the explicit input-domination
    hypothesis to specialize it to `O(T(n)^2)`.
  - [x] Keep the checked fourth-degree envelope as the simple fallback theorem
    while exposing the optimized bound through the fixed twenty-work-tape
    simulator and the parametric time-class API.
- [x] Conclude `RAM.P = P`.
- [ ] Add the space simulations and conclude RAM/TM polynomial-space
  equivalence.
- [ ] Add register-machine and Boolean-program variants and relate them by
  explicit simulations rather than as disconnected class definitions.

**Formalization hazards.** Textbook RAM simulations quietly assume unit cost;
the logarithmic cost of every register access must be charged and bounded before
a polynomial-time claim. The RAM → TM direction must store the register file on a
tape as address/value pairs and pay for search; the number of registers touched
and their bit-lengths are bounded by the log-time budget, and this bound must be
proved, not assumed. Output-length and address-length accounting must be explicit
so that the simulation's own workspace is charged.

**Small entry tasks.**

- [S] Add a `sub`/`mul` smart-constructor library and basic register-transfer
  Hoare lemmas for common gadgets (copy, conditional set, counter).
- [M] Encode a Turing-machine configuration in RAM registers with a decode
  function and prove one TM step is simulated by a fixed RAM program block.
  - [x] Fix the state/head/cell register layout and prove bounded
    decode-after-encode plus the zero frame outside the layout.
  - [x] Verify finite numeric branch selection and the fixed block's state/head-
    symbol loading phase, including compositional scratch framing.
  - [x] Prove every statically selected transition action produces the exact
    represented TM successor.
  - [x] Compose the nested state/symbol dispatch with the selected action and
    prove exact source execution plus the decoded successor.
  - [x] Add the common envelope, advertised logarithmic-cost bound, and
    compiled-RAM transfer for the complete one-step block.
  - [x] Audit uniformity, replace the bound-dependent layout with a fixed sparse
    interleaving, and prove complete decode/encode plus runtime address/loading
    correctness for a program determined solely by the TM.
  - [x] Prove sparse selected-action and nested-dispatch correctness and add a
    fixed iteration controller with exact source/compiled halting-run semantics.
  - [x] Marshal the public RAM input ABI into the sparse layout and copy the
    halted output symbol back to verdict register `R₀`.
  - [x] Derive the repeated sparse simulation core's concrete envelope and
    asymptotic `O(t log t)` logarithmic-time bound.
  - [x] Extend the concrete resource bound through the public input marshaller,
    captured-position repair, initialization, and verdict extractor.
  - [x] Package the checked end-to-end theorem as the TM-to-RAM class-level
    containment.
- [x] Encode a RAM configuration on a Turing tape with size accounting and prove
  one RAM step is simulated within a polynomial number of TM steps.
  - [x] Define and bound the canonical sparse snapshot codec.
  - [x] Implement exact lookup, update, arithmetic, and instruction dispatch.
  - [x] Compose one-step correctness into a fixed halt-aware decision loop.
  - [x] Package the complete simulator as `RAM.P ⊆ P` and hence `RAM.P = P`.

## Long-term tracks

### L1. Sum-check and `IP = PSPACE`

**Goal.** Formalize the algebraic core of interactive proofs and the theorem
`IP = PSPACE` in a clearly delimited classical, private-coin model.

**Prerequisites.** M4 TQBF/PSPACE infrastructure, M5 interactive protocols, N2
soundness amplification, and substantial finite-field polynomial support.

**Staged milestones.**

- [ ] Develop the required finite-field and low-degree polynomial evaluation API,
  including an appropriate Schwartz--Zippel theorem.
- [ ] State and prove sum-check completeness and soundness for a fixed number of
  variables and explicit individual-degree bounds.
- [ ] Arithmetize Boolean formulas over a finite field.
- [ ] Formalize the degree-reduction step needed during quantified-formula
  evaluation; naive recursive arithmetization has degree blow-up.
- [ ] Build the interactive protocol for TQBF and prove polynomial verifier time,
  polynomial communication, perfect/high completeness, and bounded soundness.
- [ ] Conclude `PSPACE subset IP` from TQBF completeness.
- [ ] Prove `IP subset PSPACE` by evaluating the finite game/acceptance recursion in
  polynomial space.

**Formalization hazards.** “Arithmetize QBF and apply sum-check” omits the central
degree-control argument. Field size must dominate all relevant degree and
soundness parameters and must itself admit a polynomial-size encoding. Mathlib's
polynomial representation may not align directly with an executable verifier, so
an evaluation-oriented layer may be needed. The theorem's completeness and
soundness constants should be explicit before class-level amplification.

**Small entry tasks.**

- [x] Prove Boolean multilinear-extension identities for one variable
  (`Complexitylib.Circuits.MultilinearExtension`: `mle₁`, `mle₁_zero`, `mle₁_one`,
  `mle₁_bool`).
- [M] Prove a univariate root-count probability bound over a finite field.
- [M] Define the sum-check verifier state and prove round-by-round invariant
  preservation.
- [L] Formalize sum-check soundness independently of TQBF.

### L2. Oracle machines and relativization

**Goal.** Make relativized complexity a mathematical part of the library and
formalize oracle worlds showing why relativizing techniques cannot settle `P` vs
`NP`.

**Prerequisites.** N1 codecs, M4 space/configuration machinery, universal-machine
enumeration, and hierarchy-style diagonalization.

**Target theorem variants.** The meaningful formal endpoints are oracle existence
theorems, for example:

- there exists an oracle `A` with `P^A = NP^A`;
- there exists an oracle `B` with `P^B != NP^B`.

The informal assertion “a proof technique relativizes” is meta-mathematical and
should not be encoded as a theorem without first defining a proof system or a
precise closure property of arguments.

**Staged milestones.**

- [ ] Define oracle TMs with a query mechanism, query-cost convention, and
  deterministic/nondeterministic execution semantics.
- [ ] Define relativized time/space classes and lift basic simulations and
  containments that genuinely relativize.
- [ ] Build clocked enumerations of oracle machines suitable for diagonalization.
- [ ] Construct a separating oracle using a unary language whose membership asks
  whether some string of a chosen length belongs to the oracle.
- [ ] Construct an equality oracle, likely via a PSPACE-complete oracle together
  with the necessary closure theorem showing both relativized classes collapse to
  PSPACE.
- [ ] State the Baker--Gill--Solovay-style barrier corollary only after both worlds
  are formalized.

**Formalization hazards.** Query length and query-tape space must be charged
consistently. Oracle constructions are stagewise and self-referential: later
stages must not alter answers used to diagonalize earlier machines. An oracle for
a complete class does not yield a collapse without proving the relevant oracle
closure and simulation results.

**Small entry tasks.**

- [S] Define a single oracle-query step and prove deterministic execution remains
  functional.
- [M] Embed ordinary machines as oracle machines that never query.
- [M] Define the standard existential unary oracle language and prove it belongs to
  `NP^A` for every oracle `A`.
- [L] Adapt the existing diagonal-machine infrastructure to clocked oracle DTMs.

### L3. Natural proofs and pseudorandomness barriers

**Goal.** Formalize a precise Razborov--Rudich-style implication connecting useful
large constructive properties to distinguishers against pseudorandom function
families.

**Prerequisites.** M1 circuit families and `P/poly`, N2 finite probability, a
cryptographic game/security layer, and explicit truth-table encodings.

**Definitions to settle first.**

- A property of `n`-input Boolean functions, represented by their `2^n`-bit truth
  tables.
- Largeness as an explicit density lower bound among all Boolean functions.
- Constructivity measured in the truth-table length `N = 2^n`, not accidentally in
  `n`.
- Usefulness against a specified circuit-size family and quantifier convention
  (“for all sufficiently large lengths” versus infinitely many lengths).
- Pseudorandom function security against a specified nonuniform circuit class,
  query model, advantage, and parameterization.

**Staged milestones.**

- [ ] Define natural properties and prove basic monotonicity/transport lemmas.
- [ ] Formalize oracle distinguishers that receive a truth table, then relate them
  to the intended PRF game.
- [ ] Prove the finite core: a large property excluding all functions in a PRF
  range yields a distinguisher with explicit advantage.
- [ ] Add constructive evaluation and circuit-size bounds to obtain a parameterized
  conditional barrier theorem.
- [ ] State a classical corollary under a clearly named strong PRF assumption. Do
  not present the PRF assumption as a proved fact.

**Formalization hazards.** There are several inequivalent “natural proof”
definitions in the literature. The strength of the PRF assumption must match the
constructivity and usefulness parameters exactly. A truth-table algorithm running
in `poly(2^n)` is exponential in `n` but is still the standard constructive scale.
Uniform algorithms, nonuniform circuits, oracle access, and sampling access should
not be silently interchanged.

**Small entry tasks.**

- [x] Define truth tables and prove there are `2^(2^n)` Boolean functions on `n`
  bits (`Complexitylib.Classes.FiniteCounting.card_boolFunc`).
- [x] Define property density as an exact rational and prove complement/union
  identities (`Complexitylib.Classes.PropertyDensity`: `density`, `density_compl`,
  `density_union_le`).
- [M] Define usefulness against `SIZE(s)` at one length.
- [M] Prove the abstract range-vs-uniform-distribution distinguisher lemma with no
  circuit assumptions.
- [L] Define a nonuniform PRF security game compatible with the existing
  negligible-function API.

### L4. Further circuit lower bounds and structural complexity

**Goal.** Extend the current Shannon, gate-elimination, Schnorr, and Valiant results
toward the major unconditional circuit lower-bound toolkit.

**Prerequisites.** M1 family classes, N2 counting, and track-specific combinatorics.

**Candidate milestones, roughly increasing in difficulty.**

- [ ] Formula-size measures and balancing; prove a Spira-style balancing theorem.
- [ ] Decision trees, restrictions, and switching operations with semantic
  preservation.
- [ ] Håstad-style switching lemma and parity not in nonuniform `AC^0`.
- [ ] Monotone circuits and an accessible monotone lower bound before attempting
  clique.
- [ ] Threshold circuits and majority gates, initially for upper-bound
  constructions.
- [ ] Karchmer--Wigderson communication relations and formula-depth equivalence.
- [ ] Pseudorandom restrictions/generators only after the probabilistic and
  cryptographic infrastructure is mature.

**Formalization hazards.** Switching lemmas are probability-heavy and indexing
conventions vary. Asymptotic class separations require converting finite lower
bounds into statements about families. Monotone lower bounds do not transfer to
general circuits. Valiant's depth-reduction lemma is not by itself a general
circuit lower bound.

**Small entry tasks.**

- [x] Define restriction composition and prove evaluation commutes with applying a
  restriction (`Complexitylib.Circuits.Restriction`: `Restriction`, `applyTo`,
  `comp`, `applyTo_comp`, `BoolFormula.restrict`, `BoolFormula.eval_restrict`).
- [x] Define formula size/leaves separately from DAG circuit size
  (`Complexitylib.Circuits.Formula`: `BoolFormula`, `size`, `leaves`,
  `leaves_le_size`).
- [x] Prove decision-tree evaluation and depth lemmas
  (`Complexitylib.Circuits.DecisionTree`: `DecisionTree`, `eval`, `depth`,
  `numLeaves`, `numLeaves_le_two_pow_depth`).
- [M] Formalize random restrictions as a finite sample space.

### L5. Counting, polynomial hierarchy, and proof complexity

**Goal.** Add the structural classes and complete problems that connect circuits,
randomness, interaction, and lower bounds.

**Prerequisites.** M1 circuits, M4 alternation/QBF, N3 reductions, and N2 counting.

**Staged directions.**

- [ ] Define the polynomial hierarchy both by alternating quantifiers and oracle
  levels, then prove equivalence at fixed levels.
- [~] Define `#P`, `GapP`, and parsimonious reductions using exact accepting-path
  counts. *(`#P` = `SharpP` and `GapP` (with `GapP.neg_mem`) in
  `Complexitylib.Classes.SharpP` done; parsimonious reductions remain.)*
- [ ] Prove elementary closure properties and relate PP to GapP sign.
- [ ] Formalize `PH subset P^#P`/Toda-style results only after polynomial
  interpolation and modular counting are available.
- [ ] Define propositional proof systems, proof length, and Cook--Reckhow
  polynomial verification.
- [~] Connect resolution proofs to CNF and establish basic width/size facts before
  attempting lower bounds. *(`Complexitylib.SAT.Resolution`: `CNF.Entails`,
  `entails_of_mem`, `entails_resolvent`. The resolution proof system is now a
  first-class inductive relation `CNF.Derives` with `entails_of_derives`
  (soundness), `refutation_sound` (a derivation of the empty clause proves
  unsatisfiability), and `derives_cons` (weakening). `resolvent_length_le` gives
  the one-step width bound; fuller width/size measures over derivations remain.)*

**Formalization hazards.** Counting paths depends on a clock and on a canonical
number of nondeterministic choices; early halting must be padded consistently.
Oracle characterizations of PH depend on the exact query model. Proof-complexity
lower bounds need a clean distinction between semantic unsatisfiability and the
syntactic derivation system.

**Small entry tasks.**

- [S] Define a clocked accepting-path count and prove invariance after halted-path
  padding.
- [x] Define `#P` functions using the existing NTM path semantics
  (`Complexitylib.Classes.SharpP`: `SharpP` class, `NTM.acceptCount_le`,
  `SharpP.le_two_pow`).
- [x] Define quantified Boolean formulas with a bounded alternation counter
  (`Complexitylib.SAT.QBF`: `QBF`, `QBF.quantDepth`, `QBF.QuantifierFree`).
- [x] Define resolution clauses and verify soundness of one resolution step
  (`Complexitylib.SAT.Resolution`: `Clause.resolvent`, `Clause.resolvent_sound`).

### L6. Descriptive complexity

**Goal.** Develop the logic-vs-complexity correspondence (after Immerman and
Fagin): characterize complexity classes by the logics that define them, so that
lower bounds become expressibility questions. The `descriptive-complexity`
project was imported wholesale as `Complexitylib.DescriptiveComplexity`; this
track grows it toward the headline theorems.

**Foundations (imported, all 0 custom axioms).**

- [x] Vocabularies/signatures and finite structures over `Fin card`
  (`DescriptiveComplexity.Vocabulary`, `.Structure`: `Vocabulary`, `FinStruct`,
  built-in `≤`/successor/min/max, `DecFinStruct`).
- [x] Isomorphisms, embeddings, substructures; isomorphism is an equivalence and
  preserves cardinality (`.Isomorphism`: `Iso.refl`/`symm`/`trans`,
  `Iso.card_eq`, `Embedding`, `IsSubstructure`).
- [x] First-order syntax and semantics with de Bruijn environments; quantifier
  rank and formula size (`.FirstOrder.Syntax`, `.Semantics`, `.Env`).
- [x] Boolean queries and order-independence, closed under Boolean operations
  (`.Query`: `BooleanQuery`, `IsOrderIndependent`, complement/inter/union).
- [x] **FO sentences define order-independent queries** (Immerman Prop 1.16):
  `.FirstOrder.Isomorphism` `Sentence.orderIndependent`, via term/formula
  isomorphism-invariance (`Term.eval_iso`, `Formula.sat_iso`).
- [x] Worked examples: directed 3-cycles with an explicit isomorphism, a binary
  string with built-in order (`.Examples`).
- [x] First-order *definable* queries and the packaged crux
  (`.Definable`: `FODefinable`, `FODefinable.orderIndependent` — FO-definable ⟹
  order-independent — with Boolean closure `complement`/`inter`/`union`).

**Milestones (open).**

- [~] Second-order logic (`SO`, `∃SO`) syntax and semantics over finite
  structures, and its order-independence. *Decomposed:*
  - [x] `SOFormula` syntax: extend `Formula` with relation-variable application
    and second-order quantifiers (relation variables de Bruijn-indexed by a
    context of arities). (`SecondOrder/Syntax.lean`: `SOFormula`, `SOSentence`,
    the FO embedding `SOFormula.ofFormula`, and `SOFormula.size`.)
  - [x] SO semantics: satisfaction under a relation-variable assignment (in
    addition to the element `Env`). (`SecondOrder/Semantics.lean`: `REnv`/`rCons`/
    `emptyREnv`, `SOFormula.Sat`, `SOSentence.Models`, and the truth-preserving FO
    embedding `SOFormula.ofFormula_sat` / `SOSentence.models_ofFormula`.)
  - [x] SO isomorphism-invariance ⟹ SO-definable queries are order-independent
    (`SecondOrder/Isomorphism.lean`: `REnv.map`/`rCons_map`, `SOFormula.sat_iso`,
    `SOSentence.models_iso`, `SODefinable`, `SODefinable.orderIndependent`).
  - [x] Mark the `∃SO` fragment (second-order existentials only, over an FO
    matrix) — the exact fragment Fagin characterizes. (`SecondOrder/Syntax.lean`:
    `SOFormula.IsFOMatrix`, `IsExistSO`, and `ofFormula_isFOMatrix`/`_isExistSO`
    placing `FO ⊆ ∃SO`.)
- [~] Encode `FinStruct` as a bit-string language (ordered structures ↔ inputs)
  to connect `BooleanQuery` to the machine-model `Language`. *Decomposed:*
  - [x] Truth-table encoding of a single relation over `Fin card` tuples, with its
    length `card ^ arity` (`Encoding.lean`: `encodeRel`, `encodeRel_length`).
  - [x] Relational part of a structure's encoding (concatenate the truth tables)
    and its total length (`encodeRels`, `encodeRels_length`).
  - [~] Full encoding: prepend `card` (and any constants) and make it computable;
    a decode/encode round-trip on ordered structures. (`Encoding.lean`: computable
    tuple enumeration `allTuples` (length `card^k`, `mem_allTuples`), computable
    relation/structure encodings `encodeRelC`/`encodeRelsC`, and the full
    `encodeStruct` (unary `card` prefix + relations) with cardinality recovery
    `encodeStruct_card` are done; encoding the constants and a full structure
    round-trip remain.)
  - [x] The induced language `⟦Q⟧ : Language` of a query (`Language.lean`:
    `queryLanguage` — the encodings of `Q`-satisfying structures — and
    `mem_queryLanguage`). This is the bridge to the machine-model `Language`.
- [ ] **Fagin's theorem** `NP = ∃SO`: the descriptive-complexity headline —
  existential second-order logic captures `NP`. *Decomposed:*
  - [~] `∃SO ⊆ NP`: given an `∃SO` sentence, an NTM that guesses the witnessing
    relations and FO-model-checks the matrix in polynomial time. (The FO
    model-checking half is done: `ModelChecking.lean` `Formula.evalB` /
    `Sentence.evalB` are computable and proven correct (`evalB_eq_sat` /
    `evalB_eq_models`). The guess-the-relations NTM and its poly-time bound remain.)
  - [ ] `NP ⊆ ∃SO`: express "there is an accepting polynomial-time computation"
    as an `∃SO` sentence (guess the computation-tableau relation; FO-check the
    local transition constraints).
- [~] **First-order reductions and projections.** The reductions of descriptive
  complexity: a target structure defined from the source by FO formulas. *Started
  (`Reduction.lean`, dimension-1 / universe-preserving case):* `FOInterpretation`
  (a defining FO formula per target relation + a source constant per target
  constant), `FOInterpretation.apply` with `apply_idInterp`, `FOReduces` between
  Boolean queries with reflexivity `FOReduces.refl`, the quantifier-free restriction
  `FOInterpretation.IsQuantifierFree` and **first-order projections** `FOProjReduces`
  (with `toFOReduces`, `refl`, and `trans`); the many-one **complement congruence**
  `FOReduces.complement`; and — the keystone — the full **de Bruijn substitution
  machinery** (`FirstOrder/Substitution.lean`: `Term.shift`, `Formula.subst`,
  `Formula.subst_sat`, and quantifier-rank preservation
  `Formula.quantifierRank_subst`) with the **transport theorem**
  `FOInterpretation.translate_sat` and **transitivity** `FOReduces.trans` (so
  FO-reducibility is a preorder); and closure of FO-definable queries under
  FO-reductions and FO-projections (`Definable.lean`:
  `FODefinable.of_reduces`/`of_projReduces`). *Remaining:*
  - [ ] General **dimension-`k`** interpretations: target universe a definable subset
    of `domᵏ` (needs a `Fin (card^k) ≃ (Fin k → Fin card)` tuple codec and an
    environment-assembly for the `arity·k` free variables), so reductions may grow
    the universe.
  - [ ] The **string-level** FO-reduction on the machine model: an FO map on
    encodings, so `FOReduces Q₁ Q₂` yields a `Language`-level many-one reduction of
    `queryLanguage Q₁` to `queryLanguage Q₂` (connects to the `MapReducesPoly`
    reduction preorder in `Classes.NP.Reduction`).
  - [ ] Refine **first-order projections** to Immerman's exact projective form (each
    target bit determined by a single source bit under a quantifier-free guard) and
    prove an FO-projection-completeness example.
- [ ] `FO ⊆ AC⁰` (and the converse for a suitable uniform `AC⁰`), linking this
  track to the circuit tracks (M3/L4). First-order projections are the reductions
  under which the `AC⁰`-complete problems are complete.
- [ ] Immerman–Vardi (`FO(LFP) = P` on ordered structures) after adding least
  fixed-point operators.

**Formalization hazards.** The structure↔bit-string encoding must fix an
ordering convention (Proviso 1.14) consistently; order-independence is what makes
a query "logical", so the encoding and the invariance results must be kept in
sync. Fagin's theorem's `∃SO ⊆ NP` direction needs a model-checking machine; the
converse needs to express an accepting computation as an `∃SO` formula.

### L7. Analysis of Boolean functions

**Goal.** Develop the Fourier analysis of Boolean functions (after Ryan O'Donnell)
as the analytic foundation for small-depth-circuit lower bounds (L4) and the
natural-proofs barrier (L3). The subtheory lives in `Complexitylib.BooleanAnalysis`
(`FourierExpansion` surface, `FourierExpansion.Defs`/`.Internal`), all 0 custom
axioms.

**Foundations (done).**

- [x] The ±1 cube `Cube n = Fin n → ZMod 2`, `BooleanFunction n = Cube n → ℝ` as a
  real inner-product space; the parity basis `χ S` and its orthonormality
  (`Defs`: `chi`, `parityFun`, `expect`, `inner`; `expect_parityFun`).
- [x] Fourier coefficients/weights, the expansion `f = ∑_S 𝓕(f,S)·χ_S`, Plancherel
  and Parseval, and mean/variance/convolution (`fourier_expansion`, `parseval`,
  `parseval_boolean`, `variance_boolean`, `fourierCoeff_convolution`).
- [x] Fourier linearity and the degree decomposition: `fourierCoeff_add`/`_smul`/
  `_sub`/`_neg`, `degreePart`, `norm_sq_degreePart`, spectral samples.
- [x] The BLR linearity test: `isLinear_iff_isMultiplicative`, `blrAcceptProb_eq`,
  `blr_soundness`, `local_correctability`.

**Chapter 2 — noise and average sensitivity (done).**

- [x] Noise stability/sensitivity and the bilinear form, with monotonicity and the
  Fourier-weight formula (`noiseStability`, `noiseStabilityBilin`,
  `noiseSensitivity`, `noiseStability_eq_sum_weight`, `noiseSensitivity_le_influence`).
- [x] The noise operator `T_ρ` with its Fourier formula `𝓕(T_ρ f, S) = ρ^|S|·𝓕(f,S)`,
  the endpoints `T_1 = id` and `T_0 f = 𝔼[f]·1`, and the (self-adjoint) operator forms
  `Stabᵨ[f] = ⟪f, T_ρ f⟫` and `Stabᵨ[f,g] = ⟪f, T_ρ g⟫` (`noiseOp`,
  `fourierCoeff_noiseOp`, `noiseOp_one`, `noiseOp_zero`, `noiseStability_eq_inner`,
  `noiseStabilityBilin_eq_inner`).
- [x] Total influence (= average sensitivity) and coordinate influence, with
  `totalInfluence_eq_sum_influence`, the Poincaré inequality
  `variance_le_totalInfluence`, and the parity checks
  `totalInfluence_parityFun`/`influence_parityFun`.
- [x] The discrete derivative `Dᵢ` and `Infᵢ[f] = ‖Dᵢ f‖²`
  (`derivative`, `fourierCoeff_derivative`, `influence_eq_norm_sq_derivative`).
- [x] The coordinate flip as a measure-preserving involution, the sensitivity
  operator `Lᵢ f = (f − f∘flipᵢ)/2` with `Infᵢ[f] = ‖Lᵢ f‖²`, and the probabilistic
  reading `Infᵢ[f] = Pr_x[f(x) ≠ f(x⊕eᵢ)]`, capped by `I[f] = 𝔼ₓ[#pivotal
  coordinates]` (`flipEquiv`, `expect_flipCoord`, `fourierCoeff_comp_flipCoord`,
  `sensitivityOp`, `fourierCoeff_sensitivityOp`,
  `influence_boolean_eq_expect_sensitive`, `totalInfluence_boolean_eq_expect_sensitive`).

**Milestones (open), roughly increasing in difficulty.**

- [~] The level-1 inequality and the FKN theorem (functions with almost all weight
  at level 1 are close to a dictator). *The elementary level-1 bounds are done:
  `𝓕(f,{i})² ≤ Infᵢ[f]`, `W¹[f] ≤ I[f]`, and the coordinate form
  `∑_i 𝓕(f,{i})² ≤ I[f]`, with the tight identity `∑_i 𝓕(f,{i})² = W¹[f]`
  (`fourierCoeff_singleton_sq_le_influence`,
  `fourierWeightAtDegree_one_le_totalInfluence`,
  `sum_fourierCoeff_singleton_sq_le_totalInfluence`,
  `sum_fourierCoeff_singleton_sq_eq_fourierWeightAtDegree_one`). The sharp
  `O(𝔼[f]²log(1/𝔼[f]))` level-1 inequality and FKN need hypercontractivity.*
- [ ] Monotone functions: `Infᵢ[f] = 𝓕(f,{i})` and the Margulis–Russo formula
  (needs a coordinate partial order on the cube in the ±1 convention).
- [~] Hypercontractivity (the `(2,4)`-norm bound) and its Fourier corollary — the
  gateway lemma for the remaining results. *The Bonami base case is done
  (`two_point_hypercontractive`: `𝔼[(T_{1/√3}(a+bx))⁴] ≤ (a²+b²)²` on one bit); the
  L^p-norm API and the coordinate-tensorization induction remain.*
- [ ] The KKL theorem (some coordinate has influence `Ω(log n / n)`).
- [ ] Friedgut's junta theorem (bounded total influence ⟹ close to a junta).
- [ ] The `AC⁰` Fourier concentration bound (Linial–Mansour–Nisan), linking this
  track to the switching-lemma work in L4.

**Formalization hazards.** The ±1 encoding flips the coordinate order (`χ(0)=+1`,
`χ(1)=−1`), so a monotonicity convention must be fixed explicitly. Hypercontractivity
is analytically heavy; prove the finite two-point inequality first and induct on
coordinates rather than importing continuous machinery. Influence has two distinct
operators — the spectral derivative `Dᵢ` (strips `i` from each frequency) and the
sensitivity operator `Lᵢ` (keeps frequencies containing `i`) — with the same squared
norm; keep them separate to avoid off-by-a-coordinate errors.

## Cross-cutting project ideas

These projects can proceed alongside the dependency-ordered tracks when they reuse
stable interfaces rather than introduce competing ones.

- **Concrete algorithms and languages:** regular languages, graph reachability,
  arithmetic languages, and bounded automata simulations provide excellent tests
  for class definitions and machine combinators.
- **Constructibility library:** close standard facts for polynomial, exponential,
  logarithmic, and composed time/space bounds.
- **Machine-model robustness:** multi-track tapes, RAM-like models, Boolean
  programs, and register machines should be related by explicit simulations rather
  than added as disconnected class definitions.
- **Communication complexity:** deterministic and randomized protocols, rectangle
  bounds, and discrepancy would support Karchmer--Wigderson and circuit lower
  bounds.
- **Cryptographic foundations:** ensembles, indistinguishability, one-way
  functions, hard-core predicates, PRGs, and PRFs can build on `Negligible` and the
  finite probability toolkit.
- **PCP and hardness of approximation:** this is a very long-term direction. Begin
  with constraint systems, gap-preserving reductions, and verifier randomness/query
  accounting; do not start from the PCP theorem statement.
- **Parameterized and fine-grained complexity:** reductions with explicit
  parameter maps and exact running times fit the library well once encoding costs
  are standardized.

## How to choose a contribution

1. Pick the earliest track containing the concept you need.
2. Check whether its prerequisites already have stable public definitions.
3. Prefer one unchecked “small entry task” or one milestone sub-lemma.
4. Write the intended public theorem statement before building proof internals.
5. Record the concrete resource bound, representation convention, and malformed
   input behavior in the module documentation.
6. Add the module to the appropriate import surface only when its API is ready.
7. Run `lake build --wfail` and the standalone single-tape validation target;
   require no errors or warnings.

For large theorem projects, a good first pull request contains definitions,
executable examples, and structural lemmas only. A second establishes the finite or
fixed-parameter theorem. The final pull request should lift that result to the
asymptotic complexity-class statement. This sequencing keeps ambitious work
reviewable and makes partial progress useful to the rest of the library.

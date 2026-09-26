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
| `f ∈ FP` | Cobham's algebra and the closure rules built on it; `iterate_mem_FP` for polynomially many iterations of a step | `Classes/P/Cobham.lean`, `Classes/Containments/Internal/FPBridge.lean`, `Classes/P/Cobham/Internal.lean` |
| `L ∈ P` | `mem_P_of_decisionFn`, `mem_P_preimage`, `P_compl`, `P_inter`, `P_union` | `Classes/P/DecisionFn.lean`, `Classes/P/Preimage.lean`, `Classes/Containments.lean` |
| `L ∈ NP` | `NP.mem_NP_of_FNP`, `mem_NP_of_poly_witness` (polynomial-time verifier, bounded witnesses) | `Classes/NP/WitnessConstruction.lean` |
| `L ∈ PSPACE` | `mem_PSPACE_of_iterate` (exponentially many iterations of an `FP` step on a polynomial-size state), `PSPACE_compl` | `Classes/Containments/Internal/SpaceIterate.lean`, `Classes/Containments/Internal/ComplementSpace.lean` |
| universal simulation | `TM.utmTM_simulates_pair` | `Models/TuringMachine/UTM/Universality.lean` |
| closure under reductions | `MapReducesPoly.mem_P`, `MapReducesPoly.mem_NP`, `mem_NP_preimage` | `Classes/NP/Reduction.lean`, `Classes/NP/Closure.lean` |

Some of these levers still live in `Internal` modules; promoting them to
stable surface modules is part of priority 2 below.

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
     (a pair-composition contract demanding finite zero-step complexities, and
     an estimator required to be correct at every clock).
   - Instantiate the remaining uninstantiated interfaces: a universal oracle
     machine for `OracleTM.IsEfficientlyUniversal`, and a list-decodable code
     family for the Nisan–Wigderson reconstruction.
2. **Reroute through characterizations and delete superseded machines.**
   `SAT ∈ NP` (about 12k lines of bespoke verifier and guess-and-verify
   machines), the Cook–Levin emitter (about 6.7k), the Tseitin transducer
   (about 6k), `PP ⊆ PSPACE` and `PH ⊆ PSPACE` (about 10k, bespoke machines),
   and the concrete languages can each be re-proved in a few hundred lines
   with the levers above plus two new `FP` combinators: bounded concatenation
   over a range, and a streaming finite-state fold. Keep public statements;
   replace proofs.
3. **One polynomial-space game-tree theorem.** Evaluating a
   polynomial-depth, exponentially branching game tree is in `PSPACE`.
   Savitch, `IP ⊆ PSPACE`, `PH ⊆ PSPACE`, `PP ⊆ PSPACE`, and `TQBF ∈ PSPACE`
   become instances, and the frame and stack encodings that Savitch and
   `IP ⊆ PSPACE` each hand-roll disappear.
4. **A logarithmic-space programming layer.** The library has no closure of
   `FL` under composition and no way to write log-space algorithms without
   hand-allocating registers; the logspace-uniform circuit generator costs
   about 50k lines for a 2k-line program, and `NL = coNL` is stalled on the
   same problem. Needed: `FL` closed under composition; a compiled loop
   language over O(1) registers of O(log n) bits with one correctness theorem;
   and a circuit encoding whose gate references are affine in loop counters.
5. **Proof automation.** Tag the `FP` and `PolyBound` closure rules for
   `fun_prop`; the PCP development alone applies them by hand about 900
   times. Try `grind` on frame, `Function.update`, and index goals. The
   library currently has no custom tactics or simp sets.
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
   reproduced exactly, and so are counted output gates, on circuits whose
   outputs are all internal gates (`Circuit.GatedOutputs`). `NeZero N` and
   `CircuitFamily.emptyOutput` stay: the fan-in-two AND/OR basis has no
   constants, so it has no zero-input circuits. The algebraic-circuits
   library, imported wholesale as `Complexitylib/Algebraic` (done, September
   2026), already works in this model. The detailed plan for phases 2 and 3
   is `docs/CircuitMigration.md`.

   The migration targets CSLib's circuit API as it will be once the author's
   pending circuit work lands, built meanwhile from an integration branch:
   bundled gate counts (#949), sequential and parallel composition (#952),
   complexity on a support (#955), inductive wires (#957), language slices
   (#954), counting via involutions (#950), and the unsubmitted relative
   complexity, circuit families with `SIZE` and `P/poly`, and Redkin's exact
   parity complexity `4(n - 1)`. CSLib's own `SIZE` and `PPoly` (De Morgan,
   as in Arora and Barak) then become the reference classes. Each phase lands
   with public statements unchanged:
   1. **Signatures and the exact correspondence.** `Basis.signature` and
      `Basis.interpretation` for every basis, and a size-preserving translation
      of typed circuits into straight-line programs over them
      (`Circuit.toStraightLine`, `Complexitylib/Circuits/StraightLine.lean`;
      done). The converse, from gated CSLib circuits, is next.
   2. **Redefine the measures and classes** (`sizeComplexity`, `SIZE`, `PPoly`,
      `CircuitFamily`, `DEPTH`, `NC`, `AC`, `TC`) over CSLib circuits, keeping
      their names, and re-prove the old statements through the correspondence.
   3. **Port the consumers by area**, replacing or retiring proofs:
      - Counting and gate elimination: Shannon's and Schnorr's bounds follow
        from CSLib's counting and algebraic-circuits' `3(n - 1)` parity bound,
        and the essential-input bound from `Circuit.essential_le_size`. The
        internal counting model (`CircDesc`) is deleted.
      - Builders (composition, hardwiring, projections, reindexing,
        multiplexer, majority, about 12.7k lines of `Fin (N + G)` offset
        arithmetic) become algebraic-circuits' substitution, restriction, and
        translation, plus CSLib's synthesis calculus.
      - AC⁰: derive parity ∉ AC⁰ for our classes from algebraic-circuits'
        Håstad development and retire the superseded normalization and
        switching internals.
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

# Complexitylib design notes

These documents explain the construction strategy behind several of the
library's largest verified machines. They complement the public theorem
statements; they are not the source of truth for current proof status.

| Document | Subject | Current status |
| --- | --- | --- |
| [N0 — Higher-level machine authoring](N0-MachineAuthoring.md) | CREI RTM evaluation, local routine lowering, and proof-engineering gates | Stable-boundary certificate adopted across UTM constructions; broader endpoint/effect work active; rose-tree lowering deferred |
| [A3 — Guess-and-Verify NTM](A3-GuessVerifyNTM.md) | SAT witness generation, pairing, and verifier composition | Implemented; the generic construction is `NP.witnessNTMConstruction` |
| [A4 — Single-Tape Simulation](A4-SingleTapeSimulation.md) | Quadratic multi-tape-to-single-tape simulation | Implemented and covered by executable regression guards |
| [A5 — Reduction Emitter](A5-ReductionEmitter.md) | Polynomial-time construction of Cook–Levin formulas | Implemented; SAT NP-completeness is proved |
| [Universal Turing Machine](UTM-design.md) | Description encoding, interpretation, fixed UTM, and clocking | Implemented through universal simulation and hierarchy support |
| [M1 — Uniform Circuits](M1-UniformCircuits.md) | Circuit serialization, validated evaluation, and the TM/circuit bridge | Implemented: `UniformPPoly_eq_P` |
| [Algebraic circuits](algebraic/README.md) | Guide to the imported algebraic-circuits library (`Complexitylib/Algebraic`) and its lower-bound developments | Imported wholesale; consolidation planned in `ROADMAP.md`, item 7 |

For current status and future work, see the
[blueprint](https://samuelschlesinger.github.io/complexitylib/blueprint/) and
the [roadmap](../ROADMAP.md). Track codes such as N0 or M1 refer to the
pre-blueprint roadmap, preserved in git history (`git show f47e3c1:ROADMAP.md`).
When a design plan is completed, preserve it if it still explains the
construction, but add a prominent status note and links to the final modules.

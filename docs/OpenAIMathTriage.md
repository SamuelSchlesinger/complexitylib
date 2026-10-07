# Further OpenAI TCS integrations

Pinned source: [openai/math](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a),
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a` (6 October 2026).
The catalogue credits OpenAI and licenses these files under Apache 2.0.

The initial three families, sensitivity separation, the complementation core,
the rational hitting-list core, and exact Fourier circuits now have integrations
and corollaries; see [OpenAIMath.md](OpenAIMath.md). Follow-up work has explicit
markers in [the roadmap](../ROADMAP.md#openai-tcs-integrations).
The unfinished choiceless port is excluded from this batch. This is an
integration queue, not an independent certification of the remaining
manuscripts. Counts below are
transitive OAI solution modules and original source lines, excluding Mathlib.
They describe the proof dependency closure, not only the named folder.
Shared dependencies mean the counts cannot be added to estimate total work.

## Next reusable layers

| Family | Proof closure | Integration and synthesis |
| --- | ---: | --- |
| [Sensitivity separation](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/Separation.lean) | 42 modules; 3,836 lines | Integrated. Source separation, the canonical decision-tree bound, and unbounded quadratic and fixed-power query-depth separations. |
| [Two-way complementation](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Main.lean) | Core: 19 modules; 4,088 lines. Extended explicit-family package: 41 modules; 8,477 lines. | Core integrated with a state-preserving `NMachine` bridge. New arbitrary-word-encoding and binary-NFA complementation bounds reuse the existing scanner, and rule out a polynomial binary complementation bound. The extended package's separate deterministic proof was not duplicated. |
| [Rational hitting lists](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Main.lean) | 53 modules; 15,304 lines | Integrated: canonical `FP` generator with exact unary input, complete rational binary output, and explicit malformed-input handling; executable matrix evaluation, finite nonzeroness and inverse-domain tests. Evaluation bit complexity remains separate. |
| [Exact Fourier circuits](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/Main.lean) | 51 modules; 19,103 lines | Integrated: complete source proof, CSLib translation, cofinal upper bound, and synthesis with the existing linear lower bound. Documentation, blueprint links, and all repository gates pass. The result concerns unrestricted scalar operations and arbitrarily large sizes. |
| [Choiceless polynomial time](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/ModelTheory/Choiceless/Separation.lean) | 26 modules; 18,461 lines | Deferred; incomplete port excluded from this batch. Finish the source port, semantic comparison, structure encodings, and finite `TM2` bridge before stating a canonical separation. See roadmap markers `OAI-CPT-*` and `OAI-TM2-BRIDGE`. |

## Larger algorithms and hardness packages

| Family | Proof closure | Required bridge or scope check |
| --- | ---: | --- |
| [Unique Games](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/UniqueGames/Theorem.lean) | 472 modules; 186,046 lines | Binary 3SAT-to-gap reduction, fixed error parameters, and its actual finite-machine contract. Reuse compiler infrastructure across hardness packages instead of duplicating it. |
| [Perfect completeness for 2-to-1 games](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/PerfectCompleteness/Theorem11.lean) | 843 modules; 254,494 lines | Align game and reduction encodings with the PCP layer. Audit completeness, soundness, and the polynomial runtime together. |
| [Optimal Max-Cut hardness](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/MaxCut/Main.lean) | 372 modules; 186,763 lines | Gap-instance semantics, encoding size, and reduction machine; derive a canonical NP-hardness theorem only after the bridge. |
| [Vertex Cover hardness](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/VertexCover/Main.lean) | 351 modules; 65,911 lines | Preserve the fixed approximation factor and graph encoding in the reduction contract. |
| [Bin packing](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Main.lean) | 284 modules; 158,527 lines | Separate additive hardness from the configuration-LP gap; audit rational bit lengths and arithmetic cost. |
| [Shortest common superstring](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Superstring/Main.lean) | 51 modules; 20,361 lines | Connect the produced word, containment specification, approximation ratio, and runtime to canonical function complexity. |
| [Randomized mean-payoff games](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RandomMean/Main.lean) | 89 modules; 27,355 lines | The source supplies an all-path-halting randomized finite machine and a success-count bound. Transfer the exact random-bit and quasipolynomial time conventions. |
| [Matching count](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/MatchingCount/BinarySolve.lean) | 112 modules; 14,589 lines | Inspect the literal binary input/output and approximation contract before choosing an FP, randomized, or counting-class surface. |
| [Loop matching](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/LoopMatching/Main.lean) | 134 modules; 17,140 lines | Audit the optimization objective and finite compiler contract, then share matching encodings where applicable. |
| [Common bases of two matroids](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatroidCounting/CommonBases.lean) | 1 module; 26,126 lines | Split the monolith into reusable probability/combinatorics layers; distinguish oracle-query and bit-operation complexity. |
| [Uniform sparsest-cut gaps](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SparsestCut/Main.lean) | 55 modules; 9,934 lines | Connect graph capacities and the relaxation value. This is an integrality-gap family, not by itself a canonical NP-hardness reduction. |

## Adjacent results to inspect after those bridges

The catalogue also has matrix-multiplication bounds, independent-set hardness,
quantum parity lower bounds, entangled-game repetition, log-concave sampling,
and memory-constrained inference. These need model-specific review before
selection. The two quantum parity entries have 21/22 modules and 3,613/3,658
lines; entangled repetition has 30 modules and 7,234 lines. Turing-degree
rigidity has a much larger recursion-theory closure (974 modules), and is a
lower priority for this complexity-library integration.

For every selected family: read the definitions, import actual solution
modules, preserve attribution, prove the canonical-model bridge and stated
corollaries, update the blueprint, then run the full repository gates. A
catalogue entry or a theorem name alone is not a substitute for that work.

## Completed slice: exact Fourier circuits

The complete solution closure now compiles on the pinned Lean/Mathlib version.
The public interface is `Complexitylib.Circuits.ExactFourier`.

- `Circuit.toCslib` preserves the entire output vector and circuit sharing.
  It charges one extra zero gate, reconciling the source's free zero wire.
- `exists_small_cslib_fourier_circuit` absorbs that constant overhead and
  proves the source's cofinal `c * n * log₂ n` upper bound in CSLib's model.
- `exists_cslib_fourier_between_bounds` combines it with the library's existing
  `(25 / 9 - ε) * n` lower bound. The source circuit size inherits that lower
  bound as well, with the one-gate difference absorbed asymptotically.
- `minimumSize_normalized_liminf` exposes the literal source minimum's
  normalized liminf. `not_eventually_le_cslib_size` rules out every positive
  eventual `n * log₂ n` lower bound in the translated scalar model.

These are exact complex scalar circuits with unrestricted coefficients.
The upper bound holds at arbitrarily large sizes, not necessarily every large
size. No uniform construction or bit-operation runtime is asserted here.
The source definitions are documented, blueprint nodes are linked, and the
full repository build, validation and API roots, linters, maintenance tests,
axiom guard, and blueprint check pass.

## Deferred: choiceless polynomial time with counting

The exploratory port did not pass its complete build and is not part of the
library snapshot. Its draft conflict-convention equivalence is also unfinished.
The following findings guide the next implementation; none certifies a
completed standard-model separation in complexitylib.

Inspection of the source definitions identifies three distinct obligations:

- `Input.query` is solvability of an explicitly given linear system over
  `ZMod 3`, on a fixed vocabulary of eight binary relations. Its definition
  applies to every finite input, and the source proves isomorphism invariance.
- `FullCPT.EvaluationDefinable` quantifies over a finite program with
  hereditarily finite sets, cardinality, comprehension, parallel updates,
  and polynomial bounds on stages and the cumulative transitive closure of
  objects occurring during evaluation. There is no fixed rank cutoff.
  The source also proves `FullCPT.query_not_definable`, using `Definable` and
  cumulative active objects in the stored states, without the extra term-root
  accounting. This second interface is the better starting point for comparing
  the usual active-object convention.
- `OrdinaryPolynomialTime` uses Mathlib's finite `TM2` stack-machine model,
  with finite stack alphabets and a polynomial bound measured in the encoded
  input length. This is a different source model from the hitting generator's
  `TM0`. Its input has a unary size header and a relation table; its runtime
  theorem is stated on encoded structures. A canonical `P` integration needs
  a stack-machine simulation and explicit handling of arbitrary binary inputs.
  The existing regular-domain guard does not by itself supply that parser.

These are source-level findings, not a completed port or a checked bridge to
complexitylib's descriptive-complexity and machine interfaces. The separate
witnessed-choice theorem is outside this initial dependency closure.

For the model comparison, Dawar, Richerby, and Rossman,
[*Choiceless Polynomial Time, Counting and the Cai–Fürer–Immerman Graphs*,
Sections 4.2–4.4](https://www.cl.cam.ac.uk/~ad260/papers/CPT-CFI.pdf),
describe resource bounds using cumulative active objects. Their presentation
also has a separate numerical universe and leaves the state unchanged on
clashing updates. The source uses finite ordinals and makes a clashing run
undefined. These differences need an explicit translation and an acceptance
argument; similar terminology alone is insufficient to identify the models.

## Completed slice: rational hitting lists

The [source model](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Model.lean)
has syntax for rational constants, variables, addition, multiplication, and
inverse. Evaluation is relational: an inverse requires an actual two-sided
inverse of the operand. `Admissible` means that some positive-dimensional
rational matrix tuple admits an evaluation; `Nonzero` additionally requires
a nonzero value. Neither definition silently totalizes inverse at a singular
matrix. A hitting output uses one common positive dimension and hits every
nonzero formula of bounded size with an invertible value.

Completed layers:

1. Imported the solution closure and exposed its finite-formula semantics.
   Proved that `Nonzero` already implies `Admissible`.
2. For every hitting list, proved that nonzeroness is equivalent to an
   invertible evaluation at one of its tuples. Positive dimension makes the
   reverse implication sound: a unit matrix is nonzero.
3. Used the list for size bound `s + 2` to test admissibility of every formula
   of size at most `s`. At a defined point, either `f` or `f + 1` is nonzero;
   a hit for either supplies a defined evaluation of `f`. This yields a
   finite domain test even for identically zero admissible formulas.
4. Added a computable determinant/adjugate evaluator with exact relational
   soundness and completeness. The generated finite tests are total and correct
   for every formula, including zero variables and empty inverse domains.
5. Proved that the inverse formula is admissible exactly when the original
   formula is nonzero. Every admissible formula also has a domain witness
   of dimension at most `256 * (n + f.size + 3)^10`.
6. Extended `Interop/Cslib/FromMultiTape` to complete string outputs, including
   the terminating blank. CSLib computations transfer with a factor-three
   time bound, and canonical `FP` is equivalent to CSLib polynomial-time
   string computation.
7. Built `Interop/Mathlib/TM0`: copying and rewinding input, simulating each
   source transition on symbol tracks, and emitting the halted output cost
   at most `2 * input.length + sourceTime + output.length + 4` CSLib steps.
   Polynomial source time and output length on every input imply canonical
   `FP`. The symbol-track encoding is shared with the depth-three bridge.
8. Added a reusable DFA guard: accepted inputs incur `2 * input.length + 2`
   source steps before execution; rejected inputs halt with empty output
   after one scan. Polynomial source bounds on a regular input domain
   therefore give a total function in canonical `FP`.
9. Proved `hittingGenerator_mem_FP` for the source's exact unary input and
   complete reduced-rational binary output. A five-state validator accepts
   precisely `true^n ++ [false] ++ true^s` for positive `n,s`; every other
   binary string produces empty output.

A full identity-testing algorithm also needs checked evaluation and rational
bit-complexity bounds, including coefficient encoding and variable-index
conventions. Polynomial-time list generation alone does not prove that
algorithmic contract.

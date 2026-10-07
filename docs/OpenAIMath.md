# Integration of OpenAI's mathematics formalizations

Source: [openai/math](https://github.com/openai/math), revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, retrieved 6 October 2026.
The source is Apache 2.0 licensed. Imported files retain attribution to OpenAI,
and their module documentation links to the exact original file. The initial
source uses Lean 4.34.1; adaptations target complexitylib's pinned toolchain.

This work starts with polynomial thresholds, finite automata, and unrestricted
depth-three Boolean circuits, and now also includes sensitivity separation,
nondeterministic automata complementation, rational hitting lists, and exact
Fourier circuits. These integrations pass the full repository quality gates.
Further TCS families are queued in [the roadmap](../ROADMAP.md#openai-tcs-integrations).
The unfinished choiceless-computation port is excluded from this batch. Source
challenge specifications containing `sorry` are not imported: integrations use
the actual solution modules and their transitive proof dependencies.

## Polynomial thresholds

The 22 proof modules from `OAI/Combinatorics/GotsmanLinial` live in
`Complexitylib/BooleanAnalysis/PolynomialThreshold/Internal`. Mechanical changes
adapt imports, namespaces, module visibility, documentation, and formatting.
Six redundant or non-normal-form `simp` attributes were removed to satisfy the
existing environment linter; the corresponding theorem statements remain.

The public [PolynomialThreshold module](../Complexitylib/BooleanAnalysis/PolynomialThreshold.lean)
uses the existing `Cube`, `BooleanFunction`, and `totalInfluence`. Its bridge
proves that the source's sensitive-edge count is exactly that total influence.
The source bound is `8 * d * sqrt n`, for multilinear real polynomials with
`sign(0) = 1`. A new checked sign-cube multilinearization removes the
multilinearity hypothesis without increasing degree or changing threshold
values. Zero dimension, zero degree, and polynomial zeros are covered.

The spectral noise and Fourier-tail bounds combine this imported result with
complexitylib's existing analysis. These are elementary consequences, with no
claim of research novelty. The noise estimate here retains dimension dependence;
the stronger dimension-free bound and learning theorem in the source paper are
not yet integrated.

## Finite automata

The 16 proof modules from `OAI/Combinatorics/Automata` are adapted under
`Models/FiniteAutomaton/OneWayLiveness/Internal`. The public definitions describe
two-way finite automata with separate endmarkers and both finite-run acceptance
conventions. Imported definitions and fields have been documented. Porting also
replaces the umbrella Mathlib import, exposes one pairing-graph definition for
Lean's module system, supplies two explicit elaboration arguments, removes a
redundant `simp` attribute, and drops unused finiteness arguments.

The [OneWayLiveness module](../Complexitylib/Models/FiniteAutomaton/OneWayLiveness.lean)
proves the source's exact exponential lower bound. A new bridge identifies the
relation-product language with an ordinary `h`-state Mathlib `NFA`. Retaining
the `NoLeft` fact in the source's asymptotic contradiction proves the stronger
impossibility statement with one-way input machines.

The new `encoded_oneWayLiveness_lower_bound` theorem goes further: **every
letter-to-word encoding preserves the exact lower bound**, with no code-length
restriction or state overhead. The proof maps a source letter to the product
of the crossing diagrams of its codeword and reuses OpenAI's relation-divisor
theorem. A recognizer need only agree on encoded words. The new binary scanner completes the fixed-alphabet consequence: for every
`n` its ordinary Mathlib NFA has exactly `9 * (n + 2)` states, while every
equivalent two-way DFA satisfies `2 ^ (n / 31) ≤ 4 * (s + δ) ^ 2`. Both
acceptance conventions are covered. The proof concerns the NFA's full binary
language: agreement on encoded relation words suffices for the lower bound.
No two-way DFA simulator is needed. These results are checked deductions
from the imported proof; no claim about priority in the literature is made.

## Nondeterministic complementation

The 19-module dependency closure of
[`TwoWayAutomata/Main.lean`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Main.lean)
is adapted under `Models/FiniteAutomaton/Complementation/Internal`.
The source theorem, algebraic image argument, and finite-path representation
are retained. The port narrows the umbrella Mathlib import and supplies the
specific semigroup, idempotent-corner, and finite-union cardinality imports.

The [Complementation module](../Complexitylib/Models/FiniteAutomaton/Complementation.lean)
uses the existing `NMachine` model with zero-step finite-run acceptance.
A checked state-preserving translation reconciles the source's numbered
endmarkers, move codes, and swapped configuration coordinates.
It proves that the complement of the ordinary `h`-state Mathlib liveness NFA
requires `2 ^ ((h - 2) / 127) ≤ 2 * (s + 1)` states in any two-way NFA,
for `h ≥ 2`. The one-way endmarker construction also gives a witness with
`h + 3` states and no left moves.

The new encoded-word theorem preserves this lower bound through **every
letter-to-word code**, with no code-length factor. Applying it to the existing
binary scanner gives `2 ^ (n / 127) ≤ 2 * (s + 1)` for every two-way NFA
recognizing the complement of its full binary language, while the original
ordinary NFA has `9 * (n + 2)` states. An additional corollary rules out any
polynomial state bound for complementing ordinary binary NFAs into two-way
NFAs. These deductions combine the new import with the earlier liveness
integration; they make no claim about the source authors' awareness or priority.

## Threshold-weight infrastructure

The [ThresholdWeight module](../Complexitylib/BooleanAnalysis/ThresholdWeight.lean)
proves that a uniform margin `γ` and per-feature correlation bound `ε` imply
`γ ≤ ε * ∑ j, |a j|`, over any nonempty finite domain. This is the reusable
duality step for the depth-three consequence. The application supplies the
correlation bound and
transports it from the hard slice to the full language through width-preserving
CNF substitution. For each `s ≥ 0`, eventually width at most
`ceil (3 * (s + 1) * sqrt (n / 5))` forces margin-one coefficient weight at
least `2 ^ (4 * (s + 1) * sqrt (n / 5)) / 6`, where `n / 5` is natural division.
An additional checked corollary removes the margin hypothesis for integer
threshold representations, using the shifted score `2 * t + 1`. An integer
bias is included as the coefficient of the empty CNF.

The new `LowerBound.NormalForm` bridge transports both weight results to
complexitylib's canonical `CNF`. Literal signs and evaluation agree, and
converted width is bounded by the canonical clause-length width. It also
turns an OR of canonical CNFs into a source circuit with exactly one gate
per clause, one per CNF, and one top gate; the unrestricted lower bound
therefore applies with that total gate count.

## Unrestricted depth-three circuits

The complete 175-module proof is adapted under
`Circuits/DepthThree/LowerBound`, with the machine and circuit definitions in
`LowerBound/Defs.lean`. The public theorem supplies the explicit finite
multitape polynomial-time decider and the eventual `2 ^ (A * sqrt n)` gate
lower bound for every `A > 0`. Its OR-AND-OR gates have unrestricted fan-in,
free literals and constants, and sharing of bottom and middle gates.

The port uses the current pinned dependencies, replaces the umbrella Mathlib
import, and documents the imported definitions and data fields. Five internal
definitions were renamed to camelCase. Redundant or non-normal-form simp
attributes and unused instance hypotheses were removed; two instances and ten
helper definitions were exposed for Lean's module system. The complete port
passes its scoped build and environment lint without exemptions.

The imported machine is finite and its polynomial time bound is proved.
The new generic machine bridge proves membership in complexitylib's canonical
`P`: one binary track per source tape and symbol gives an exact
`2 * n + T + 3` CSLib time bound, followed by the existing canonical simulation.
The general circuit-model bridge is also complete: CSLib circuits over the
unbounded AND/OR signature may have arbitrary wiring, shared gates, and free
edge negations. Their selected output has an equivalent formula with no
greater depth and size at most `(2 * (n + gates) + 1) ^ (depth + 1)`.

The full-language threshold-weight corollaries are checked. Balanced padding
now supplies another checked consequence: an exactly balanced family hard for
both OR-AND-OR and AND-OR-AND circuits, with the same eventual
`2 ^ (A * sqrt n)` lower bound for every `A > 0`. It reuses the existing
`Algebraic.Cutwidth.balancePad` and its accepted-input count. The dual circuit
interpretation explicitly exchanges AND and OR and complements the bottom
inputs, preserving the number of gates. Both the original and balanced languages are
now proved members of canonical `P`; the original one-bit evaluator is in `FP`.

The new formula normalization converts every depth-three formula, in one
output polarity, to an OR of canonical CNFs using at most twice the tree size
plus one source gate. Balanced hardness covers both polarities. Absorbing
the polynomial normalization overhead preserves the eventual
`2 ^ (A * sqrt n)` lower bound for every `A > 0` in the general CSLib model.
The theorem `exists_balanced_language_in_P_cslib_depth_three_lower_bound`
bundles canonical `P`, exact balance, and this circuit bound.

## Sensitivity and exact query depth

The 42 source modules in the dependency closure of
[`Sensitivity/Separation.lean`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/Separation.lean)
are adapted under `BooleanAnalysis/Sensitivity`. The public definitions use
ordinary finite Boolean functions. Sensitivity is a maximum over inputs;
it is distinct from the average sensitivity in the polynomial-threshold result.
Block sensitivity counts disjoint nonempty blocks whose flips change the output.
The port adds documentation, narrows imports, and factors the labeling argument
through an arbitrary-size lemma to avoid expanding finite enumeration during
elaboration on the current toolchain.

The public [Sensitivity module](../Complexitylib/BooleanAnalysis/Sensitivity.lean)
exports the quantitative ratio, the failure of every constant quadratic bound,
and the source's fixed-power family with an exponent strictly above two.
New proofs connect these results to the existing `DecisionTree.On` model:
`sensitivity f ≤ blockSensitivity f ≤ tree.depth` for every exact tree.
A separate construction proves that every Boolean function on `n` bits has
an exact tree of depth at most `n`, including `n = 0`.

The resulting query-depth corollaries say that for every positive `C` there
is a nonconstant function requiring depth greater than `C * sensitivity²`,
and that one fixed exponent above two works along a family whose required
exact query depths tend to infinity. These are checked deductions from the
source result and the canonical-model bridge, without a claim of new priority.

## Rational hitting lists and inverse domains

The 53 source modules in the closure of
[`RationalHitting/Main.lean`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Main.lean)
are adapted under `Complexitylib/RationalHitting`. The port narrows Mathlib
imports, supplies documentation, follows term and predicate naming conventions,
and updates proofs for the current localization, vector, and Bird determinant
APIs. It also removes unused instance parameters and redundant simplification
attributes to satisfy the repository linters. The construction retains OpenAI's
affine-pencil, rank-expansion, cyclotomic-specialization, exact arithmetic,
and finite compiler arguments.

The [public module](../Complexitylib/RationalHitting.lean) exposes an executable
`hittingList n s`. It hits every size-`s` nonzero noncommutative rational formula
with an invertible value, and its matrix dimension is at most
`256 * (n + s + 1)^10`. The complete encoding includes dimension, tuple count,
and every reduced rational entry; its length is bounded by a fixed constant
times `(n + s + 1)^104` for `n ≥ 1`.

`exists_uniform_generator` supplies one fixed finite-state Mathlib `TM0`
machine generating these exact encodings in polynomially many ordinary
transitions. The input parameters are unary, with a distinguished separator.
The [canonical polynomial-time interface](../Complexitylib/RationalHitting/PolynomialTime.lean)
now proves `hittingGenerator_mem_FP`. On input `true^n ++ [false] ++ true^s`,
with `n,s ≥ 1`, this total function returns exactly `encodeOutput (hittingList n s)`.
Every malformed string returns the empty string.

The reusable [Mathlib machine bridge](../Complexitylib/Interop/Mathlib/TM0.lean)
now transfers a finite source computation from `x` to `y` in time `T` to a
binary CSLib computation in time `2 * x.length + T + y.length + 4`.
Its symbol encoding is shared with the depth-three simulator. The reverse
CSLib bridge now preserves complete output strings, including the terminating
blank, and proves `mem_FP_iff_computableInTimeAndSpace`. A reusable
[DFA guard](../Complexitylib/Interop/Mathlib/TM0/Guard.lean) extends polynomial
source bounds on any regular input domain to a total `FP` function. It scans
without changing the input, rejects with empty output, and rewinds accepted
words before executing the source. The extra source time is `2 * input.length + 2`.
The hitting generator instantiates this with a checked five-state unary validator.

New proofs in the [evaluation interface](../Complexitylib/RationalHitting/Evaluation.lean)
establish several consequences:

- `Nonzero` already implies `Admissible`; clients need no additional domain
  hypothesis to use a hitting list on a nonzero formula.
- A hitting list for size `s` detects nonzeroness by a defined invertible
  evaluation at one of its tuples. Positive matrix dimension is essential
  for the reverse implication.
- A list for size `s + 2` detects admissibility of every size-`s` formula.
  At a defined point, either `f` or `f + 1` is nonzero. A hit for either gives
  a defined evaluation of `f`, including when `f` is identically zero.
- `admissible_inv_iff_nonzero` identifies nonzeroness with the existence of
  a defined evaluation of the inverse formula. The forward direction uses
  a genuine two-sided inverse; the converse uses the invertible hitting value.
- `Admissible.exists_dimension_le` supplies a domain witness of dimension
  at most `256 * (n + f.size + 3)^10`. Thus a nonempty domain always has a
  polynomial-dimensional witness, independently of coefficient magnitudes.
- `Formula.evalMatrix?` computes the exact partial semantics using rational
  determinants and adjugates. Its soundness and completeness are proved;
  every singular inverse operand is rejected.
- `Formula.admissible?` and `Formula.nonzero?` are terminating Boolean tests
  with unconditional correctness theorems and computed `Decidable` instances.
  These also cover formulas with zero variables. They are finite decision
  procedures, not enumeration with an inconclusive timeout.

No polynomial bit-time bound for these evaluation tests is asserted. That
requires a separate analysis of encoded formulas, coefficients, intermediate
rational values, and matrix evaluation. Polynomial-time generation of the
list alone does not establish polynomial-time identity testing. The domain
and testing results are checked deductions, without a claim that the source
authors were unaware of them.

## Exact Fourier circuits

The 51 solution modules in the closure of
[`FourierCircuit/Main.lean`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/Main.lean)
are adapted under `Complexitylib/Circuits/ExactFourier`. The port retains the
finite-win, matrix-price, positive-generation, cascade, packing, amplification,
and Fourier-transfer arguments. Adaptations narrow Mathlib imports, document
the constructions, remove unused parameters and redundant simplification
attributes, and follow the repository's module and formatting conventions.

The [public interface](../Complexitylib/Circuits/ExactFourier.lean) states the
source bound precisely: for every `c > 0` and lower threshold `N`, some
`n ≥ max N 2` admits an exact Fourier circuit with fewer than
`c * n * log₂ n` gates. Equivalently, the literal minimum scalar gate count
divided by `n * log₂ n` has liminf zero. This concerns arbitrarily large sizes;
it does not supply the corresponding upper bound at every sufficiently large
size. Each addition, subtraction, and multiplication by an arbitrary complex
scalar costs one gate. Coefficients are unrestricted, and neither a uniform
construction nor a bit-operation runtime is asserted.

The new [CSLib bridge](../Complexitylib/Circuits/ExactFourier/Cslib.lean)
preserves every output and circuit sharing. The source supplies a free zero
wire; its CSLib translation charges exactly one additional zero gate. The
public upper bound absorbs that constant overhead, so it holds for ordinary
CSLib gate count over the explicit scalar signature.

New synthesis with the existing DFT lower-bound development gives:

- Every sufficiently large source circuit, and every CSLib scalar circuit
  with fan-in at most two, has more than `(25 / 9 - ε) * n` gates for each
  `ε > 0`. The proof transfers the library's polynomial-operation lower bound
  and absorbs the extra zero gate when returning to the source model.
- For every positive `ε,c` and every size threshold, there is an exact CSLib
  Fourier circuit satisfying both that linear lower bound and the imported
  `c * n * log₂ n` upper bound.
- No positive eventual `n * log₂ n` lower bound holds for these unrestricted
  scalar circuits. This is a direct consequence of the cofinal upper bound;
  it makes no assertion about bounded-coefficient circuits.

These are checked transfers and deductions, with no claim that the source
authors were unaware of them. The full library build, validation and API roots,
linters, axiom guard, and blueprint check pass for this integration.

## Integration status

All three initial families, their listed corollaries, and the machine and
circuit bridges are implemented. Sensitivity separation and its decision-tree
consequences, together with nondeterministic complementation and its binary
corollaries, extend this first batch. The rational hitting-list core and its
finite decision procedures are integrated, and its total binary generator is
proved in canonical `FP`. Polynomial bit complexity for formula evaluation
remains separate. Exact Fourier circuits now transfer to CSLib and combine
with the library's existing linear lower bounds. Further TCS formalizations
and their unproved model bridges are recorded in [the queue](OpenAIMathTriage.md)
and the roadmap's `OAI-*` follow-up markers.

At the final pre-commit check, the required build passed with 8,321 jobs,
including all five executable validation roots and seven isolated API checks.
Both linters and all 29 maintenance tests passed. The axiom guard checked
116,578 declarations, including 85,545 theorems and no project axioms, across
4,188 project modules; only standard axioms were used. The blueprint check
validated 1,407 nodes and 5,146 Lean references. These checks validate the
local integration; they do not establish mathematical priority or complete
the remaining integration queue.

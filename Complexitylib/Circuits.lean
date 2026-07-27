/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Basic
public import Complexitylib.Circuits.BitString
public import Complexitylib.Circuits.Composition
public import Complexitylib.Circuits.Dependency
public import Complexitylib.Circuits.DecisionTree
public import Complexitylib.Circuits.DecisionTree.Finite
public import Complexitylib.Circuits.DecisionTree.NormalForm
public import Complexitylib.Circuits.DecisionTree.Path
public import Complexitylib.Circuits.DecisionTree.Restriction
public import Complexitylib.Circuits.Formula
public import Complexitylib.Circuits.Spira
public import Complexitylib.Circuits.FormulaEncoding
public import Complexitylib.Circuits.CircuitFormula
public import Complexitylib.Circuits.Restriction
public import Complexitylib.Circuits.RandomRestriction
public import Complexitylib.Circuits.BranchingProgram
public import Complexitylib.Circuits.Barrington
public import Complexitylib.Circuits.BarringtonS5
public import Complexitylib.Circuits.BarringtonBridge
public import Complexitylib.Circuits.BarringtonRepr
public import Complexitylib.Circuits.BarringtonLength
public import Complexitylib.Circuits.BarringtonCompiler
public import Complexitylib.Circuits.BranchingProgramEncoding
public import Complexitylib.Circuits.BarringtonCodeGenerator
public import Complexitylib.Circuits.BarringtonFamily
public import Complexitylib.Circuits.BarringtonConverse
public import Complexitylib.Circuits.BarringtonTyped
public import Complexitylib.Circuits.CircuitFormula.Family
public import Complexitylib.Circuits.MultilinearExtension
public import Complexitylib.Circuits.NormalForm
public import Complexitylib.Circuits.NormalForm.Operations
public import Complexitylib.Circuits.NormalForm.Restriction
public import Complexitylib.Circuits.AndOrNot
public import Complexitylib.Circuits.BasisHom
public import Complexitylib.Circuits.Threshold
public import Complexitylib.Circuits.Monotone
public import Complexitylib.Circuits.KarchmerWigderson
public import Complexitylib.Circuits.Encoding
public import Complexitylib.Circuits.Family
public import Complexitylib.Circuits.Encoding.Family
public import Complexitylib.Circuits.Encoding.Machine
public import Complexitylib.Circuits.XOR
public import Complexitylib.Circuits.XOR.Restriction
public import Complexitylib.Circuits.EssentialInput
public import Complexitylib.Circuits.Shannon
public import Complexitylib.Circuits.LowerBound
public import Complexitylib.Circuits.Schnorr
public import Complexitylib.Circuits.DepthClasses
public import Complexitylib.Circuits.AC0
public import Complexitylib.Circuits.Nondeterminism
public import Complexitylib.Circuits.Hardwiring
public import Complexitylib.Circuits.Unrolling
public import Complexitylib.Circuits.Valiant

/-! # Circuit Complexity Library

A Lean 4 formalization of classical results in Boolean circuit complexity,
built on Mathlib.

## The circuit model

A `Circuit B N M G` is an acyclic Boolean circuit over basis `B` with `N`
primary inputs, `M` outputs, and `G` internal gates. The circuit's `size`
is `G + M`: internal and output gates are counted, while primary-input
vertices and per-edge negation flags are not. For an arbitrary basis,
`sizeComplexityWithTop` is the minimum size of any circuit computing a Boolean
function, with `⊤` for an unrealizable function. The natural-valued
`sizeComplexity` interface is available for complete bases.

## Main results

* **Functional completeness** (`CompleteBasis Basis.unboundedAndOr`):
  Unbounded fan-in AND/OR (with free negation) can compute every Boolean
  function, via DNF construction.

* **Shannon counting lower bound** (`shannon_lower_bound_circuit`):
  For `N ≥ 6`, there exists a Boolean function on `N` inputs that cannot
  be computed by any fan-in-2 AND/OR circuit with fewer than `2^N / (5N)`
  gates.

* **Essential-input lower bound**
  (`Circuit.card_essentialInputs_le_totalFanIn`):
  Over every basis, essential inputs are bounded by total fan-in. For bounded
  fan-in `k` AND/OR this yields `n' ≤ k · size`.

* **Schnorr's XOR lower bound** (`schnorr_lower_bound_circuit`):
  Any fan-in-2 AND/OR circuit computing N-input XOR (or its complement)
  requires at least `2(N − 1)` internal gates.

* **CNF/DNF lower bound for XOR** (`DNF.two_pow_le_complexity_of_xorBool`,
  `CNF.two_pow_le_complexity_of_xorBool`): Any DNF (resp. CNF) computing N-input XOR
  requires at least `2^{N-1}` terms (resp. clauses).

* **Nondeterministic quantification** (`sizeComplexity_existsQuantify_le`):
  If `f` has circuit complexity `s`, then `∃ x ∈ {0,1}^k, f(x,y)` has
  circuit complexity at most `2^k · (s + 1)`.  Combined with the Shannon
  upper bound (`sizeComplexity_existsQuantify_le_min`).

* **Valiant's depth reduction** (`Valiant.depth_reduction`):
  In any acyclic digraph with `S` edges and depth at most `2^k`, for any `r ≤ k`
  one can remove a set of at most `r · S / k` edges so that the remaining
  digraph has depth at most `2^k / 2^r`.

* **Barrington's theorem** (`barrington_equivalence`):
  Variable-bounded logarithmic-depth formula families are exactly
  variable-bounded polynomial-length width-`5` permutation branching-program
  families as sets of typed `BoolFunFamily`. The finite forward theorem
  `barrington_representation_depth_four` gives the textbook length bound
  `4 ^ depth`, and `barrington_quadratic_of_log_depth` specializes it to `n²`
  at depth at most `log₂ n`.
  `barringtonCompile_representation` supplies the same finite theorem through
  an explicit executable compiler rather than an existential choice.
  `NC1_subset_Width5BP` applies the typed theorem directly to actual nonuniform
  `NC1` circuit families. The older
  `barrington_equivalence_onTotalAssignments` remains as an explicitly named
  theorem for syntax families whose domain really is `ℕ → Bool`.

* **Spira formula balancing** (`BoolFormula.exists_spira_balanced`):
  Every finite Boolean formula has an equivalent formula of logarithmic depth
  and polynomial tree size, with explicit quantitative bounds.

* **Monotone Karchmer--Wigderson correspondence**
  (`KarchmerWigderson.Protocol.exists_protocol_depth_iff_formula_depth`):
  root communication protocols and monotone formulas exist at exactly the same
  depth.

* **Threshold simulation** (`AC_subset_TC`):
  Exact basis transport embeds every nonuniform `AC^i` family in nonuniform
  `TC^i` without changing circuit size or depth.

* **Finite AC0 obstruction for parity**
  (`AC0Formula.parity_counting_obstruction`):
  Iterated width switching, exact staged-restriction semantics, and the
  decision-tree lower bound for parity yield a division-free finite counting
  inequality for every depth-bounded unbounded AND/OR formula computing parity.

## Module structure

Public modules (definitions a reviewer should read):

* `Complexitylib.Circuits.Basic` — `BitString`, `BoolFunFamily`, `Circuit`, `Basis`, `Gate`,
  `CompleteBasis`, `Realizable`, `sizeComplexityWithTop`, `sizeComplexity`,
  `wireDepth`, `depth`
* `Complexitylib.Circuits.BitString` — canonical bridges between `BitString n`
  and `List Bool`
* `Complexitylib.Circuits.Composition` — serial circuit composition with exact
  additive size, exact semantics, and additive depth
* `Complexitylib.Circuits.Dependency` — the finite circuit dependency DAG,
  its canonical topological order, and its edge bound by total fan-in
* `Complexitylib.Circuits.DecisionTree.Restriction` — semantic restriction
  with nonincreasing decision-tree depth
* `Complexitylib.Circuits.DecisionTree.Finite` — arity-indexed decision trees
  with exact finite restriction semantics
* `Complexitylib.Circuits.DecisionTree.NormalForm` — exact decision-tree
  compilation to CNF and DNF with depth-controlled width
* `Complexitylib.Circuits.RandomRestriction` — the finite sparse-restriction
  sample space with exact cardinalities
* `Complexitylib.Circuits.Spira` — finite nonuniform formula balancing with
  explicit logarithmic-depth and polynomial-size bounds
* `Complexitylib.Circuits.CircuitFormula` — exact selected-output unfolding from
  fan-in-two circuit DAGs to Boolean formulas, with a factor-two depth bound
* `Complexitylib.Circuits.FormulaEncoding` — canonical iterative postfix formula
  codec with exact round trips and code length
* `Complexitylib.Circuits.CircuitFormula.Family` — family-level unfolding and
  the typed-`NC1` bridge to width-`5` branching programs
* `Complexitylib.Circuits.Family` — circuit families, list semantics, pointwise
  size/depth bounds, and the polynomial-size characterization
* `Complexitylib.Circuits.BarringtonConverse` — balanced branching-program
  evaluation and the explicitly total-assignment equivalence
* `Complexitylib.Circuits.BarringtonTyped` — variable-bounded fixed-arity
  formula/program families and the typed nonuniform Barrington equivalence
* `Complexitylib.Circuits.BarringtonCompiler` — executable finite `S₅` search
  and formula-to-program compilation with the `4 ^ depth` bound
* `Complexitylib.Circuits.BranchingProgramEncoding` — canonical seven-bit
  permutation ranks, instruction/program codecs, and exact size bounds
* `Complexitylib.Circuits.BarringtonCodeGenerator` — the total bitstring-level
  formula-code-to-program-code target for the remaining `FL` implementation
* `Complexitylib.Circuits.Encoding` — canonical proof-free encoding, validation,
  and iterative evaluation of fan-in-two AND/OR circuits
* `Complexitylib.Circuits.Encoding.Family` — tagged encoding and evaluation at
  every input length, including the explicit empty-input answer
* `Complexitylib.Circuits.Encoding.Machine` — total linear-time validation and
  tape staging plus the verified end-to-end quadratic serialized circuit-family
  evaluator
* `Complexitylib.Circuits.Encoding.Machine.NatCode` — framed, one-way
  terminated-unary natural-code emission from a preserved binary value, with
  reusable zero scratch and explicit time/all-prefix-space bounds
* `Complexitylib.Circuits.AndOrNot.Defs` — `AndOrOp`, `Basis.unboundedAndOr`,
  `Basis.boundedAndOr`, `Basis.andOr2`
* `Complexitylib.Circuits.AndOrNot` — functional completeness and a semantic,
  total-fan-in size bound for compiling unbounded AND/OR to fan-in two
* `Complexitylib.Circuits.BasisHom` — exact semantics-, size-, depth-, and
  topology-preserving circuit transport between compatible bases
* `Complexitylib.Circuits.Threshold` — unweighted threshold gates, strict
  majority, and exact unbounded-AND/OR simulation
* `Complexitylib.Circuits.Monotone` — typed monotone formulas, locality,
  monotonicity, and essential-input leaf lower bounds
* `Complexitylib.Circuits.KarchmerWigderson` — rectangle-indexed deterministic
  protocols and the depth-exact monotone formula correspondence
* `Complexitylib.Circuits.NormalForm.Defs` — `Literal`, `CNF`, `DNF`,
  clause/term count, and width
* `Complexitylib.Circuits.NormalForm` — CNF/DNF lower bound for XOR
  (`two_pow_le_complexity_of_xorBool`)
* `Complexitylib.Circuits.NormalForm.Operations` — semantic negation,
  conjunction, and disjunction operations on CNFs and DNFs
* `Complexitylib.Circuits.NormalForm.Restriction` — semantic CNF/DNF
  simplification with nonincreasing width and clause/term count
* `Complexitylib.Circuits.XOR` — `Schnorr.xorBool` (N-input parity)
* `Complexitylib.Circuits.EssentialInput` — `IsEssentialInput`, `essentialInputs`
* `Complexitylib.Circuits.DepthClasses` — `DEPTH`, the nonuniform `NC`, `AC`,
  and `TC` hierarchies, and the aliases `NC0`, `NC1`, `AC0`, and `TC0`
* `Complexitylib.Circuits.AC0` — the `AC0` class plus finite nonuniform
  negation-normal formulas, circuit normalization, exact restrictions,
  width-sensitive switching, finite staged iteration, and the exact parity
  counting obstruction
* `Complexitylib.Circuits.Nondeterminism.Defs` — `existsQuantify`, `forallQuantify`
* `Complexitylib.Circuits.Hardwiring` — exact-size prefix hardwiring
* `Complexitylib.Circuits.Unrolling` — bounded machine-configuration layouts,
  initialization, verified trace tiling, typed acceptance circuits, exact-size
  fixed-choice hardwiring, and parallel strict-majority amplification

Theorem modules (re-export definitions + main results):

* `Complexitylib.Circuits.AndOrNot` — functional completeness of AND/OR
* `Complexitylib.Circuits.Shannon` — Shannon counting lower bound
* `Complexitylib.Circuits.LowerBound` — gate elimination lower bound
* `Complexitylib.Circuits.Schnorr` — Schnorr's XOR lower bound
* `Complexitylib.Circuits.Nondeterminism` — nondeterministic quantification complexity bounds
* `Complexitylib.Circuits.Valiant` — Valiant's depth reduction lemma for digraphs

Internal modules contain proof machinery (CircDesc, DNF construction,
restriction/elimination arguments) and are not intended for direct use.
-/

@[expose] public section

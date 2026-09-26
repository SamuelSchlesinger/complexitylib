/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Vocabulary
public import Complexitylib.DescriptiveComplexity.Structure
public import Complexitylib.DescriptiveComplexity.Isomorphism
public import Complexitylib.DescriptiveComplexity.Query
public import Complexitylib.DescriptiveComplexity.Env
public import Complexitylib.DescriptiveComplexity.FirstOrder
public import Complexitylib.DescriptiveComplexity.SecondOrder
public import Complexitylib.DescriptiveComplexity.SecondOrder.Reduction
public import Complexitylib.DescriptiveComplexity.SecondOrder.Definable
public import Complexitylib.DescriptiveComplexity.SecondOrder.PolynomialTime
public import Complexitylib.DescriptiveComplexity.Definable
public import Complexitylib.DescriptiveComplexity.Reduction
public import Complexitylib.DescriptiveComplexity.Reduction.Encoding
public import Complexitylib.DescriptiveComplexity.Interpretation
public import Complexitylib.DescriptiveComplexity.Interpretation.Pullback
public import Complexitylib.DescriptiveComplexity.Interpretation.Composition
public import Complexitylib.DescriptiveComplexity.Problem
public import Complexitylib.DescriptiveComplexity.TaggedReduction
public import Complexitylib.DescriptiveComplexity.TaggedReduction.Encoding
public import Complexitylib.DescriptiveComplexity.Problems.Coloring
public import Complexitylib.DescriptiveComplexity.Problems.Interpretations
public import Complexitylib.DescriptiveComplexity.Problems.Copies
public import Complexitylib.DescriptiveComplexity.Encoding
public import Complexitylib.DescriptiveComplexity.Encoding.Positions
public import Complexitylib.DescriptiveComplexity.Encoding.Arithmetic
public import Complexitylib.DescriptiveComplexity.Encoding.PolynomialTime
public import Complexitylib.DescriptiveComplexity.Encoding.Validity
public import Complexitylib.DescriptiveComplexity.Encoding.Decoding
public import Complexitylib.DescriptiveComplexity.ModelChecking
public import Complexitylib.DescriptiveComplexity.ModelChecking.Encoded
public import Complexitylib.DescriptiveComplexity.ModelChecking.PolynomialTime
public import Complexitylib.DescriptiveComplexity.Circuit
public import Complexitylib.DescriptiveComplexity.Circuit.Encoding
public import Complexitylib.DescriptiveComplexity.Circuit.Validity
public import Complexitylib.DescriptiveComplexity.AC0
public import Complexitylib.DescriptiveComplexity.Language
public import Complexitylib.DescriptiveComplexity.Examples

/-!
# Descriptive complexity

Foundations of descriptive complexity (after Immerman), imported from the
`descriptive-complexity` project and grown inside this corpus: vocabularies
(signatures), finite structures, isomorphisms, injective homomorphisms and
substructures, first-order logic (syntax, semantics, substitution,
isomorphism-invariance), second-order logic (syntax, semantics,
isomorphism-invariance), Boolean queries and order-independence, FO- and existential
SO-definable queries, arity-preserving relation renaming and existential SO
intersection and union through prefix merging, first-order reductions and their
quantifier-free restriction, Boolean relation witnesses, verified matrix evaluation,
exact truth-table certificate encodings, and polynomial-time existential-SO
binary checkers with polynomial certificate bounds, proving `∃SO ⊆ NP` against
the existing machine class,
SO transport through universe-preserving interpretations, tagged tuple
interpretations with exact size, formula pullback, and composition up to
isomorphism, invariant decision problems and tagged reduction preorders, computable
first-order model checking, bit-string encodings of finite structures and the
languages they induce (`queryLanguage`), exact computable decoding with rejection
of malformed inputs, arithmetic bit positions, polynomial-time encoding access,
and proofs that valid encodings and every FO-definable query language belong to
the machine class `P`. The encoded sentence evaluator has a one-bit verdict in `FP`.
Universe-preserving FO interpretations now give `FP` maps on the full binary
encodings and induce polynomial-time many-one reductions. Combining these with
an ESO target witness transfers known NP-hardness to machine NP-completeness.
Tagged interpretations also have exact arithmetic encoding semantics, including
their packed constants; their polynomial-time machine bound remains open.
Worked examples include an SO
definition and executable witness checker for bipartiteness, the two-copy graph
interpretation, and a disjoint-copy
reduction preserving bipartiteness.

Finite quantifier expansion connects the FO syntax to the existing `AC0Formula`
representation, with correct table-input semantics, exact polynomial tree size,
and depth bounded independently of universe size. These trees have actual circuit
realizations of exactly the same size and at most one extra depth layer. The
computable encoding layout reads `encodeStruct` itself. A constant-depth validator
rejects malformed inputs. The resulting circuits cover every input length and
prove `FODefinable.queryFamily_mem_AC0` for the existing nonuniform circuit class.

The headline foundational result is `DescriptiveComplexity.Sentence.orderIndependent`
(Immerman Proposition 1.16): first-order sentences define order-independent
queries. Together with the proved nonuniform `FO ⊆ AC⁰` inclusion and machine
`FO ⊆ P` inclusion, this supports the capture program. Fagin's upper direction
`∃SO ⊆ NP` is proved; the converse tableau construction remains planned.
The staged expansion plan and its sources are recorded in `docs/DescriptiveComplexity.md`.
-/

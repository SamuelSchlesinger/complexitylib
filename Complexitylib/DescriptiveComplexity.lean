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
public import Complexitylib.DescriptiveComplexity.Definable
public import Complexitylib.DescriptiveComplexity.Reduction
public import Complexitylib.DescriptiveComplexity.Encoding
public import Complexitylib.DescriptiveComplexity.ModelChecking
public import Complexitylib.DescriptiveComplexity.Language
public import Complexitylib.DescriptiveComplexity.Examples
public import Complexitylib.DescriptiveComplexity.SecondOrder.Reduction
public import Complexitylib.DescriptiveComplexity.SecondOrder.Definable
public import Complexitylib.DescriptiveComplexity.SecondOrder.PolynomialTime
public import Complexitylib.DescriptiveComplexity.Interpretation
public import Complexitylib.DescriptiveComplexity.Interpretation.Pullback
public import Complexitylib.DescriptiveComplexity.Interpretation.Composition
public import Complexitylib.DescriptiveComplexity.Problem
public import Complexitylib.DescriptiveComplexity.TaggedReduction
public import Complexitylib.DescriptiveComplexity.Problems.Coloring
public import Complexitylib.DescriptiveComplexity.Problems.Interpretations
public import Complexitylib.DescriptiveComplexity.Problems.Copies
public import Complexitylib.DescriptiveComplexity.Encoding.Positions
public import Complexitylib.DescriptiveComplexity.Encoding.Arithmetic
public import Complexitylib.DescriptiveComplexity.Encoding.PolynomialTime
public import Complexitylib.DescriptiveComplexity.Encoding.Validity
public import Complexitylib.DescriptiveComplexity.Encoding.Decoding
public import Complexitylib.DescriptiveComplexity.ModelChecking.Encoded
public import Complexitylib.DescriptiveComplexity.ModelChecking.PolynomialTime
public import Complexitylib.DescriptiveComplexity.Circuit
public import Complexitylib.DescriptiveComplexity.Circuit.Encoding
public import Complexitylib.DescriptiveComplexity.Circuit.Validity
public import Complexitylib.DescriptiveComplexity.AC0

/-!
# Descriptive complexity

Foundations of descriptive complexity (after Immerman), imported from the
`descriptive-complexity` project and grown inside this corpus: vocabularies
(signatures), finite structures, isomorphisms, injective homomorphisms and
substructures, first-order logic (syntax, semantics, substitution,
isomorphism-invariance), second-order logic (syntax, semantics,
isomorphism-invariance), Boolean queries and order-independence, FO-definable
queries, first-order reductions and quantifier-free projections, computable
first-order model checking, bit-string encodings of finite structures and the
languages they induce (`queryLanguage`), and worked examples.

The headline foundational result is `DescriptiveComplexity.Sentence.orderIndependent`
(Immerman Proposition 1.16): first-order sentences define order-independent
queries. This is the substrate for the planned logic-vs-complexity
correspondences (Fagin's theorem `NP = ∃SO`, `FO ⊆ AC⁰`, etc.).
-/

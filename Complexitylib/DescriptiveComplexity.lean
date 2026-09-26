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

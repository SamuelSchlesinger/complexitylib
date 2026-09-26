/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.Syntax
public import Complexitylib.DescriptiveComplexity.SecondOrder.Semantics
public import Complexitylib.DescriptiveComplexity.SecondOrder.Isomorphism
public import Complexitylib.DescriptiveComplexity.SecondOrder.Renaming
public import Complexitylib.DescriptiveComplexity.SecondOrder.Connectives
public import Complexitylib.DescriptiveComplexity.SecondOrder.ModelChecking
public import Complexitylib.DescriptiveComplexity.SecondOrder.Encoding
public import Complexitylib.DescriptiveComplexity.SecondOrder.Certificate

/-!
# Second-order logic over finite structures

Aggregates second-order syntax, semantics, isomorphism invariance, relation
renaming, existential-prefix connectives, and verified matrix evaluation with
Boolean relation witnesses. Canonical truth-table certificates have exact length,
and existential-SO sentences have verified binary certificate checkers with
polynomial witness bounds. The downstream `SecondOrder.PolynomialTime` module
proves their polynomial-time machine bound and Fagin's upper direction `∃SO ⊆ NP`.
The converse tableau construction remains planned.
-/

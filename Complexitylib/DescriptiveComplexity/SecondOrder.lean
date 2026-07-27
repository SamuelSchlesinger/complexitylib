/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.DescriptiveComplexity.SecondOrder.Syntax
public import Complexitylib.DescriptiveComplexity.SecondOrder.Semantics
public import Complexitylib.DescriptiveComplexity.SecondOrder.Isomorphism

/-!
# Second-order logic over finite structures

Aggregates the second-order logic modules (currently syntax; semantics and
isomorphism-invariance to follow), the machinery for Fagin's theorem `NP = ∃SO`
on roadmap track L6.
-/

@[expose] public section

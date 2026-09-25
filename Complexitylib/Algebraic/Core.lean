/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Fin
public import Complexitylib.Algebraic.Signature
public import Complexitylib.Algebraic.Interpretation
public import Complexitylib.Algebraic.Homomorphism
public import Complexitylib.Algebraic.Program
public import Complexitylib.Algebraic.Circuit
public import Complexitylib.Algebraic.Semantics
public import Complexitylib.Algebraic.Support
public import Complexitylib.Algebraic.Cost
public import Complexitylib.Algebraic.Substitution
public import Complexitylib.Algebraic.Parallel
public import Complexitylib.Algebraic.Iteration
public import Complexitylib.Algebraic.Translation

/-!
# Core circuit API

This is the focused import for CSLib's finite-arity signatures, shared
programs and circuits, and this library's semantics, costs, and translations.
Concrete bases, analyses, and lower-bound developments remain in their own
modules so downstream users do not need the full research surface.
-/

@[expose] public section

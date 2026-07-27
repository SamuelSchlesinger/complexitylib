/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.AC0.Defs
public import Complexitylib.Circuits.AC0.NormalForm
public import Complexitylib.Circuits.AC0.Normalization
public import Complexitylib.Circuits.AC0.Restriction
public import Complexitylib.Circuits.AC0.Switching
public import Complexitylib.Circuits.AC0.Switching.Collection
public import Complexitylib.Circuits.AC0.Switching.Parity
public import Complexitylib.Circuits.AC0.Iteration
public import Complexitylib.Circuits.AC0.Parity
public import Complexitylib.Circuits.DepthClasses

/-!
# The class AC⁰

Compatibility surface for `Complexity.AC0`: Boolean-function families computed
by constant-depth, polynomial-size circuit families of unbounded fan-in AND/OR
gates with free negation on wires. The class definition and basic API live in
`Complexitylib.Circuits.DepthClasses`.

This surface also exports the finite nonuniform normalization and switching
substrate: negation-normal unbounded formulas, exact finite restrictions,
arity-indexed decision trees, a finite sparse-restriction sample space, and
unfolding of a selected circuit output to an equivalent formula without
increasing depth. Duplicate signed incidences are canonicalized before
unfolding, yielding an explicit polynomial tree-size bound at constant circuit
depth.

The switching surface includes both an elementary ambient-arity encoding and
a width-sensitive finite Håstad encoding for CNFs and DNFs. De Morgan duality,
semantic cleanup of contradictory terms or tautological clauses, and the
decision-tree lower bound for parity under arbitrary finite restrictions are
all connected in exact cardinality form. A staged compiler iterates this layer
through arbitrary finite depth-bounded formulas, with exact semantics, an exact
first-moment identity for surviving variables, and a division-free counting
obstruction for every finite formula computing parity. The remaining separation
step is the family-level arithmetic specialization proving nonuniform parity is
not in `AC0`.
-/

@[expose] public section

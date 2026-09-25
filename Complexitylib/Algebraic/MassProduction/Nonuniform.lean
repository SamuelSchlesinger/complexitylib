/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.PhaseSelection
public import Complexitylib.Algebraic.MassProduction.Nonuniform.SortedPropagation
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BatchLookupBound
public import Complexitylib.Algebraic.MassProduction.Nonuniform.CandidateSelection
public import Complexitylib.Algebraic.MassProduction.Nonuniform.DuplicateFlags
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BatchOrCircuit
public import Complexitylib.Algebraic.MassProduction.Nonuniform.MenuSelection
public import Complexitylib.Algebraic.MassProduction.Nonuniform.PaddedLinePoints
public import Complexitylib.Algebraic.MassProduction.Nonuniform.PowerLayout
public import Complexitylib.Algebraic.MassProduction.Nonuniform.UniversalGeometricPhase
public import Complexitylib.Algebraic.MassProduction.Nonuniform.SchedulerCircuit
public import Complexitylib.Algebraic.MassProduction.Nonuniform.ScheduledRecovery
public import Complexitylib.Algebraic.MassProduction.Nonuniform.FiniteBound
public import Complexitylib.Algebraic.MassProduction.Nonuniform.RealTheorem

/-!
# Nonuniform mass production with the sharp exponential-range coefficient

`existsUniversalPhaseMenu` proves one fixed menu works for every legal
occupied state and target tuple. `phaseMenuCandidateCount_le` bounds the
number of examined candidate lines by `capacity * (2 + 3 * addressBits)`.
`HalfClean.existsHalfSelection` gives exactly half-sized progress with
disjoint recovery lines.

`Propagation.circuit_cost` and `Broadcast.payloadCircuit_cost_le` prove
concrete linear-size propagation primitives. `BatchLookup.existsCircuit`
proves complete batched lookup, including repeated queries and fixed output
wires, with linear record-count dependence and polynomial width factors.
`CandidateSelection.circuit_selects` selects a successful candidate and a
clean prefix. `MarkDuplicates.circuit_correct` detects all key collisions and
returns their flags to the original record positions. Both have explicit
circuit-size bounds.
`DuplicateFlags.circuit_eval_iff` adds the ordering identifiers automatically.
`BatchOr.existsCircuit` proves shared OR aggregation with repeated or absent
source keys and a linear record-count bound.
`MenuSelection.circuit_selects` assembles point-conflict detection, request
aggregation, and candidate selection for an enumerated menu, preserving
request payloads and proving an explicit size bound. Its contract requires
one successful candidate and distinct point slots within each request.
`PaddedLinePoints` enumerates fixed-direction punctured lines, using at most
one gate per point bit and marking the zero scalar invalid.
`GeometricPhase.existsUniversalPhase` connects these components into one
fixed geometric phase circuit for every encoded state under the packing
budget. It preserves request data and generated point lists and accepts the
rounded-up half prefix. `GeometricPhase.circuit_cost_le` includes generation,
evaluation, and selection in one explicit bound.
`Scheduler.existsCircuit` completes initialization, free buffer compaction,
and every halving phase for a power-of-two batch. It adds fixed identifiers,
so repeated targets and payloads require no distinctness premise. Its output
retains all original records and disjoint recovery point lists, and its cost
is `requests * 2^width` times an explicit fixed polynomial in bit widths and
the ceiling logarithm of the request count.
`ScheduledRecovery.existsCircuit` connects the scheduler to an exact
high-rate resource bank, scatter/gather, padded XOR recovery, and restoration
of the original request order. It reads encoded copy, point, basis-bit, and
suffix metadata from supplied wires. Its bound charges each actual resource
evaluation once and includes all scheduler/routing overheads.
`FiniteBound.booleanMassComplexity_le_explicit` includes the shared offline
prefix lookup, proves existence of the high-rate code and complete source
placement, chooses index widths canonically, and synthesizes every resource
function. It gives a full Boolean mass-complexity bound on raw inputs under
finite numerical field/dimension/direction conditions. The corresponding
parametric bound accepts the proved sharp shorter-function estimate from
`LupanovRuntime.normalizedResourceBound`.
`sharpExponentialMassProduction` proves the coefficient `1/(1-gamma) + o(1)`
for every rational copy exponent below one in an exact integer precision
formulation. `realSharpMassProduction` proves the manuscript's full real-rate
and additive-error statement. Both include the complete finite construction,
parameter selection, code rate and rounding, resource synthesis, polynomial
overhead absorption, and restriction to every allowed positive copy count.
-/

@[expose] public section

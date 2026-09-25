/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.FiniteMassProductionCircuit

/-!
# Mass-production routing assembly

Compatibility umbrella for the concrete mass-production circuit pipeline.
The implementation is split into scheduled wiring, scatter and gather record
assembly, resource-stage composition, pipeline assembly, and the final
hardwired finite circuit.
-/

@[expose] public section

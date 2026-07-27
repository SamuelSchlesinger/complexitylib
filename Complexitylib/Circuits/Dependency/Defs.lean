/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Basic
public import Complexitylib.Mathlib.Digraph
public import Mathlib.Data.Fintype.BigOperators

/-!
# Circuit dependency graphs -- definitions

The dependency graph of a circuit has one vertex for every primary input,
internal gate, and output gate. Each gate-input occurrence contributes an
edge from the referenced wire to the gate that reads it. Repeated occurrences
of the same wire at the same gate collapse in the graph's edge set, while
`Circuit.totalFanIn` continues to count them with multiplicity.
-/

@[expose] public section

namespace Complexity

namespace Circuit

variable {B : Basis} {N M G : ℕ} [NeZero N] [NeZero M]

/-- Total number of gate-input occurrences, including output gates. -/
def totalFanIn (c : Circuit B N M G) : ℕ :=
  (∑ i, (c.gates i).fanIn) + ∑ j, (c.outputs j).fanIn

/-- One internal- or output-gate input occurrence in a circuit. -/
abbrev DependencyOccurrence (c : Circuit B N M G) :=
  (Σ i : Fin G, Fin (c.gates i).fanIn) ⊕
    (Σ j : Fin M, Fin (c.outputs j).fanIn)

/-- The directed dependency edge represented by one gate-input occurrence. -/
def dependencyEdge (c : Circuit B N M G) :
    DependencyOccurrence c → Fin (N + G + M) × Fin (N + G + M)
  | .inl ⟨i, input⟩ =>
      (⟨((c.gates i).inputs input).val, by omega⟩,
        ⟨N + i.val, by omega⟩)
  | .inr ⟨j, input⟩ =>
      (⟨((c.outputs j).inputs input).val, by omega⟩,
        ⟨N + G + j.val, by omega⟩)

/-- The finite set of dependency edges. Parallel occurrences collapse here. -/
def dependencyEdges (c : Circuit B N M G) :
    Finset (Fin (N + G + M) × Fin (N + G + M)) :=
  Finset.univ.image c.dependencyEdge

/-- The directed graph whose edges are the circuit's wire dependencies. -/
def dependencyGraph (c : Circuit B N M G) :
    Digraph (Fin (N + G + M)) where
  Adj source target := (source, target) ∈ c.dependencyEdges

instance (c : Circuit B N M G) :
    DecidableRel c.dependencyGraph.Adj := by
  intro source target
  change Decidable ((source, target) ∈ c.dependencyEdges)
  exact inferInstance

end Circuit

end Complexity

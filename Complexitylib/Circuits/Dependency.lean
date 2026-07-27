/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Dependency.Defs
public import Complexitylib.Circuits.Dependency.Internal

/-!
# Circuit dependency graphs

This module exposes the circuit DAG as a finite directed graph. Vertices are
primary inputs, internal gates, and output gates. Edges point from each
referenced wire to the gate that reads it.

## Main results

* `Circuit.dependencyGraph_adj_val_lt` -- every edge follows the circuit's
  canonical index order.
* `Circuit.dependencyGraph_isAcyclic` -- the dependency graph is acyclic.
* `Circuit.dependencyGraph_edge_card_le_totalFanIn` -- distinct edges are
  bounded by total fan-in.
-/

@[expose] public section

namespace Complexity

namespace Circuit

variable {B : Basis} {N M G : ℕ} [NeZero N] [NeZero M]

/-- Dependency-graph adjacency is membership in the finite edge set. -/
@[simp] theorem dependencyGraph_adj_iff
    (c : Circuit B N M G)
    {source target : Fin (N + G + M)} :
    c.dependencyGraph.Adj source target ↔
      (source, target) ∈ c.dependencyEdges :=
  Iff.rfl

/-- Every dependency edge points from a smaller to a larger vertex index. -/
theorem dependencyGraph_adj_val_lt
    (c : Circuit B N M G)
    {source target : Fin (N + G + M)}
    (edge : c.dependencyGraph.Adj source target) :
    source.val < target.val :=
  dependencyGraph_adj_val_lt_internal c edge

/-- The dependency graph of every well-formed circuit is acyclic. -/
theorem dependencyGraph_isAcyclic
    (c : Circuit B N M G) :
    c.dependencyGraph.IsAcyclic :=
  dependencyGraph_isAcyclic_internal c

/-- The generic graph edge enumeration recovers the circuit edge set. -/
@[simp] theorem dependencyGraph_edgeFinset
    (c : Circuit B N M G) :
    c.dependencyGraph.edgeFinset = c.dependencyEdges :=
  dependencyGraph_edgeFinset_internal c

/-- The number of distinct dependency edges is at most total fan-in.

The inequality can be strict because multiple inputs of one gate may read the
same wire, while a digraph stores only one copy of an edge. -/
theorem dependencyGraph_edge_card_le_totalFanIn
    (c : Circuit B N M G) :
    c.dependencyGraph.edgeFinset.card ≤ c.totalFanIn :=
  dependencyGraph_edge_card_le_totalFanIn_internal c

end Circuit

end Complexity

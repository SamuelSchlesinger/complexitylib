/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Internal.Valiant

/-! # Valiant's Depth Reduction Lemma

The **length** of a directed path is the number of nodes in it. The
**depth** of a finite directed graph is the length of a longest simple path.

**Lemma** (Valiant, 1977). *In any acyclic directed graph with `S` edges and
depth `d = 2 ^ k`, for any `1 ≤ r ≤ k`, it is possible to remove
`r * S / k` edges so that the depth of the resulting graph does not
exceed `d / 2 ^ r`.*

Reference: L. G. Valiant, *Graph-theoretic arguments in low-level
complexity*, MFCS 1977. Stated as Lemma 1.4 in Jukna, *Boolean
Function Complexity*.

The theorem states acyclicity explicitly. This is the circuit-relevant case
and prevents a bounded-depth hypothesis from hiding a directed cycle.

The proof machinery — canonical labelings, the edge partition by
first-differing bit, averaging, and the relabeling-after-removal
bound — lives in `Complexitylib.Circuits.Internal.Valiant`.
-/

@[expose] public section

namespace Complexity

namespace Valiant

open Digraph

/-- **Valiant's Depth Reduction Lemma** (Valiant, 1977).

In any finite acyclic directed graph `G` with `S` edges and depth at most
`2 ^ k`, for any `r ≤ k`, there exists a set `F` of edges such
that:

* `F` is a subset of the edge set,
* `k * F.card ≤ r * S` (equivalent to `|F| ≤ r * S / k` without
  integer division), and
* after removing `F`, the resulting digraph has depth at most
  `2 ^ k / 2 ^ r`.

The explicit acyclicity hypothesis matches the DAG setting in which Jukna's
canonical-labeling argument applies. -/
theorem depth_reduction
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj]
    {k r : Nat} (hrk : r ≤ k)
    (hac : IsAcyclic G)
    (hd : G.depth ≤ 2 ^ k) :
    ∃ F : Finset (V × V),
      F ⊆ G.edgeFinset ∧
      k * F.card ≤ r * G.edgeFinset.card ∧
      (G.deleteEdges F).depth ≤ 2 ^ k / 2 ^ r := by
  obtain ⟨I, hIsub, hIcard, hIsum⟩ := exists_r_levels_small G hrk hac hd
  refine ⟨I.biUnion fun i => levelEdges G k i, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨i, _, hie⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp hie).1
  · calc k * (I.biUnion fun i => levelEdges G k i).card
        ≤ k * ∑ i ∈ I, (levelEdges G k i).card :=
          Nat.mul_le_mul_left k Finset.card_biUnion_le
      _ ≤ r * G.edgeFinset.card := hIsum
  · have hbound := depth_deleteEdges_levelEdges_le G hac hd I hIsub
    rw [hIcard] at hbound
    have hpow : (2 : ℕ) ^ k / 2 ^ r = 2 ^ (k - r) :=
      Nat.pow_div hrk (by decide)
    rw [hpow]
    exact hbound

end Valiant

end Complexity

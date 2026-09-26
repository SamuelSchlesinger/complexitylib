/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.AlgEdge

/-!
# Iterating a round

Amplification runs a round logarithmically many times. On the algorithm's side
that is an iteration of one `FP` function; on the abstract side it is an
iterate `T^[k]` of the round's transformation (`Amplifier.iter` unfolds to
one). This module says the two agree, for any round function that computes its
transformation.

## Main results

- `Complexity.iterate_encGraph` — iterating the algorithm writes the iterated
  graph
- `Complexity.iterate_mem_FP_encGraph` — and the iteration is an `FP` function
-/

@[expose] public section

namespace Complexity

variable {α : Type} [Fintype α] [DecidableEq α]

/-- **Iterating the algorithm writes the iterated graph.** -/
theorem iterate_encGraph {f : List Bool → List Bool}
    {T : ConstraintGraph α → ConstraintGraph α}
    (hstep : ∀ G : ConstraintGraph α, f (encGraph G) = encGraph (T G)) :
    ∀ (k : ℕ) (G : ConstraintGraph α), f^[k] (encGraph G) = encGraph (T^[k] G) := by
  intro k
  induction k with
  | zero => intro G; rfl
  | succ k ih =>
      intro G
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hstep, ih]

/-- **The iteration is an `FP` function.** The bound the iteration rule wants is
supplied on the *graphs*, where the round's size bounds live, rather than on
their encodings. -/
theorem iterate_mem_FP_encGraph {f init ruler width : List Bool → List Bool}
    {T : ConstraintGraph α → ConstraintGraph α}
    (hf : f ∈ FP) (hinit : init ∈ FP) (hruler : ruler ∈ FP) (hwidth : width ∈ FP)
    (hstep : ∀ G : ConstraintGraph α, f (encGraph G) = encGraph (T G))
    (hinitG : ∀ z, ∃ G : ConstraintGraph α, init z = encGraph G)
    (hbound : ∀ (z : List Bool) (G : ConstraintGraph α), init z = encGraph G →
      ∀ n ≤ (ruler z).length, (encGraph (T^[n] G)).length ≤ (width z).length) :
    (fun z => f^[(ruler z).length] (init z)) ∈ FP := by
  refine Cobham.iterate_mem_FP hf hinit hruler hwidth ?_
  intro z n hn
  obtain ⟨G, hG⟩ := hinitG z
  rw [hG, iterate_encGraph hstep]
  exact hbound z G hG n hn

end Complexity

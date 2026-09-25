/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Neq.Preimage

/-!
# An AND-gate lower bound for crown-graph collision

The crown graph on two copies of `Fin N` joins a left vertex to a right vertex
exactly when their labels differ.  Its graph-collision function asks whether
some marked left vertex and some marked right vertex are adjacent.

On assignments marking exactly one vertex on each side, graph collision is
Boolean inequality.  Pulling the positive-generator set problem back to this
one-hot slice therefore gives `Neq.problem N` exactly, and the inequality
lower bound transfers to monotone AND/OR circuits computing graph collision.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace CrownCollision

/-- The graph-collision function for the crown graph `K_{N,N}` with the
diagonal perfect matching removed. -/
def function (assignment : Fin (N + N) → Bool) : Bool :=
  decide (∃ left right : Fin N,
    left ≠ right ∧
      assignment (Fin.castAdd N left) = true ∧
      assignment (Fin.natAdd N right) = true)

/-- The positive-generator set problem for crown-graph collision. -/
abbrev problem (N : Nat) : SetProblem (Fin (N + N) → Bool) :=
  monotoneProblem (function (N := N))

/-- Mark exactly the two vertices selected by an ordered left/right pair. -/
def oneHotPair (edge : Neq.Ground N) : Fin (N + N) → Bool :=
  Fin.addCases
    (fun left => decide (left = edge.1))
    (fun right => decide (right = edge.2))

/-- Pulling crown-graph collision back to one-hot left/right assignments gives
the row/column inequality problem exactly. -/
theorem preimage_eq_neq :
    (problem N).map
      (AndOr.preimageHomomorphism (oneHotPair (N := N))).map =
        Neq.problem N := by
  unfold Problem.map problem monotoneProblem Neq.problem
  congr 1
  · funext input
    refine Fin.addCases (motive := fun input =>
      (AndOr.preimageHomomorphism (oneHotPair (N := N))).map
          {assignment | assignment input = true} =
        Fin.addCases Neq.row Neq.column input)
      (fun left => ?_) (fun right => ?_) input
    · ext edge
      simp only [AndOr.preimageHomomorphism_map, Set.mem_preimage,
        Fin.addCases_left]
      change oneHotPair edge (Fin.castAdd N left) = true ↔
        edge.1 = left
      unfold oneHotPair
      rw [Fin.addCases_left, decide_eq_true_eq]
      exact eq_comm
    · ext edge
      simp only [AndOr.preimageHomomorphism_map, Set.mem_preimage,
        Fin.addCases_right]
      change oneHotPair edge (Fin.natAdd N right) = true ↔
        edge.2 = right
      unfold oneHotPair
      rw [Fin.addCases_right, decide_eq_true_eq]
      exact eq_comm
  · ext edge
    change function (oneHotPair edge) = true ↔ edge.1 ≠ edge.2
    unfold function
    rw [decide_eq_true_eq]
    constructor
    · rintro ⟨left, right, different, leftTrue, rightTrue⟩
      have leftEq : left = edge.1 := by
        simpa only [oneHotPair, Fin.addCases_left,
          decide_eq_true_eq] using leftTrue
      have rightEq : right = edge.2 := by
        simpa only [oneHotPair, Fin.addCases_right,
          decide_eq_true_eq] using rightTrue
      simpa [leftEq, rightEq] using different
    · intro different
      refine ⟨edge.1, edge.2, different, ?_, ?_⟩
      · simp only [oneHotPair, Fin.addCases_left, decide_eq_true_eq]
      · simp only [oneHotPair, Fin.addCases_right, decide_eq_true_eq]

/-- Every AND/OR circuit computing crown-graph collision on two copies of
`Fin (2 ^ n)` uses at least `n` AND gates, even when OR gates are free. -/
theorem and_lowerBound
    (circuit : Circuit AndOr.signature
      ((2 ^ n) + (2 ^ n)) g 1)
    (computes : ∀ assignment,
      circuit.eval AndOr.boolInterpretation assignment 0 =
        function assignment) :
    n ≤ circuit.cost AndOr.andCost := by
  apply Neq.and_lowerBound_of_preimage
    (f := oneHotPair (N := 2 ^ n))
    (image := preimage_eq_neq (N := 2 ^ n))
  exact (Problem.computesMembership_iff_constructs
    (problem (2 ^ n)) circuit).mp
      ((monotoneProblem_computesMembership_iff
        (function (N := 2 ^ n)) circuit).mpr computes)

end CrownCollision
end Fusion
end Algebraic

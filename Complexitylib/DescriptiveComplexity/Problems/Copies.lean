/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.TaggedReduction
public import Complexitylib.DescriptiveComplexity.Problems.Coloring

/-!
# Disjoint graph copies as a tagged reduction

Taking a positive number of disjoint copies preserves and reflects bipartiteness.
The forward coloring ignores the tag; the reverse coloring restricts to one copy.
This supplies a reduction with a genuinely larger universe and tests the tagged
interface against an independently defined graph property. It is not a hardness
result.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity.GraphQuery

section

open TaggedFOInterpretation

/-- A fixed positive number of disjoint copies of the source graph. -/
def disjointCopies (copies : Nat) (hcopies : 0 < copies) :
    TaggedFOInterpretation Vocabulary.graph Vocabulary.graph copies 1 where
  tags_pos := hcopies
  dim_pos := by decide
  relFormula := fun _ tags =>
    if tags 0 = tags 1 then
      .relApp 0 (fun j => .var (finProdFinEquiv (j, 0)))
    else .falsum
  constTag := Fin.elim0
  constCoord := Fin.elim0

/-- Edges stay within one copy and agree there with the source graph. -/
theorem disjointCopies_edge (copies : Nat) (hcopies : 0 < copies)
    (A : FinStruct Vocabulary.graph) (x y : Fin (copies * A.card ^ 1)) :
    Edge ((disjointCopies copies hcopies).apply A) x y ↔
      (elementEquiv A.card copies 1 x).1 = (elementEquiv A.card copies 1 y).1 ∧
      Edge A ((elementEquiv A.card copies 1 x).2 0)
        ((elementEquiv A.card copies 1 y).2 0) := by
  simp only [Edge, apply, disjointCopies]
  split <;> simp_all [Formula.Sat, Term.eval, relationEnv, Formula.falsum_sat,
    apply_ite, ite_apply]

/-- A positive disjoint union of copies is bipartite exactly when the source is. -/
theorem disjointCopies_bipartite (copies : Nat) (hcopies : 0 < copies)
    (A : FinStruct Vocabulary.graph) :
    Bipartite ((disjointCopies copies hcopies).apply A) ↔ Bipartite A := by
  constructor
  · rintro ⟨color, hcolor⟩
    let embed (x : Fin A.card) : Fin (copies * A.card ^ 1) :=
      (elementEquiv A.card copies 1).symm (⟨0, hcopies⟩, fun _ => x)
    refine ⟨fun x => color (embed x), ?_⟩
    intro x y hxy
    exact hcolor _ _ (by simpa [disjointCopies_edge, embed] using hxy)
  · rintro ⟨color, hcolor⟩
    refine ⟨fun x => color ((elementEquiv A.card copies 1 x).2 0), ?_⟩
    intro x y hxy
    exact hcolor _ _ ((disjointCopies_edge copies hcopies A x y).mp hxy).2

/-- Bipartiteness as an invariant decision problem. -/
def bipartiteProblem : DecisionProblem Vocabulary.graph :=
  .ofExistSODefinable Bipartite bipartite_existSODefinable

/-- Disjoint copies give a first-order reduction of bipartiteness to itself. -/
def disjointCopiesReduction (copies : Nat) (hcopies : 0 < copies) :
    TaggedFOReduction bipartiteProblem bipartiteProblem where
  tags := copies
  dim := 1
  interpretation := disjointCopies copies hcopies
  correct A := (disjointCopies_bipartite copies hcopies A).symm

end

end Complexity.DescriptiveComplexity.GraphQuery
